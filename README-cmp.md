<!--
README-cmp
-->

```coq
Module Fallacy.

Inductive compare_result :=
  | win
  | eq
  | lose.

Inductive comparable_human := winner | loser.

Definition comparer : Type := 
  comparable_human -> comparable_human -> compare_result.

Definition compare : comparer := fun p₀ p₁ => 
  match (p₀, p₁) with
  | (winner, loser) => win
  | (loser, winner) => lose
  | _ => eq
  end.

Fact cmp_not_comm : forall (p₀ p₁ : comparable_human), 
  compare p₀ p₁ = win <-> compare p₁ p₀ = lose.
Proof.
  split.
  - intros H. destruct p₀; destruct p₁.
    + discriminate.
    + reflexivity.
    + discriminate.
    + discriminate.
  - intros H. destruct p₀; destruct p₁.
    + discriminate.
    + reflexivity.
    + discriminate.
    + discriminate.
Qed.

Definition my_compare : comparer := fun p₀ p₁ =>
  match (p₀, p₁) with
  | (_, loser) => lose
  | (loser, _) => lose
  | _ => eq
  end.

Fact compare_with_loser_is_loser : forall p₀ : comparable_human,
  my_compare p₀ loser = lose.
Proof.
  intros p₀.

  destruct p₀.
  - reflexivity.
  - reflexivity.
Qed.

Fact my_cmp_isnot_cmp : 
  exists p₀ p₁, ~ (my_compare p₀ p₁ = win <-> my_compare p₁ p₀ = lose).
Proof.
  unfold not.
  
  exists loser.
  exists winner.

  intros Hiff.

  remember compare_with_loser_is_loser as H.
  apply Hiff in H as Hiff'.
  discriminate.
Qed.

End Fallacy.
```
