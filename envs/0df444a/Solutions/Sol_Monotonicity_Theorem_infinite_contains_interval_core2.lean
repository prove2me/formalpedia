-- Prove2me | solution 1 for Monotonicity_Theorem.infinite_contains_interval_core2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-14T23:47:47.545449+00:00
-- url     : https://prove2.me/submissions/4b77fa9e-0fc9-420c-8bf8-0ceb9fcf500f

import Definitions.Def_Monotonicity_Theorem_Framework2

open Monotonicity_Theorem

-- An infinite set built from points and intervals (in the o-minimal sense)
-- contains a nondegenerate open interval. Proved by induction on the
-- finite-union structure: empty and point cases are finite, a union splits
-- infiniteness to one side, and a degenerate interval is empty.
theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (hDef : FiniteUnionOfPointsAndIntervals A) (hInf : Set.Infinite A) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧ ∀ x : Power R 1, openInterval a b x → A x := by
  induction hDef with
  | empty =>
      exfalso
      have hfin : Set.Finite (fun _ : Power R 1 => False) := Set.finite_empty
      exact hInf hfin
  | point a =>
      exfalso
      have hsing : pointSet a = {(fun _ => a : Power R 1)} := by
        ext x
        simp only [pointSet, Set.mem_singleton_iff]
        constructor
        · intro h
          funext i
          have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
          have hi : i = (0 : Fin 1) := Fin.ext hi0
          rw [hi]
          exact h
        · intro h
          rw [h]
          rfl
      have hfin : Set.Finite (pointSet a) := by
        rw [hsing]
        exact Set.finite_singleton _
      exact hInf hfin
  | interval a b =>
      by_cases hlt : Endpoint.lt a b
      · exact ⟨a, b, hlt, fun x hx => hx⟩
      · exfalso
        have hempty : openInterval a b = ∅ := by
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          cases a with
          | negInf =>
              cases b with
              | negInf => exact hx.2
              | finite v => exact hlt trivial
              | posInf => exact hlt trivial
          | finite u =>
              cases b with
              | negInf => exact hx.2
              | finite v => exact hlt (lt_trans hx.1 hx.2)
              | posInf => exact hlt trivial
          | posInf => exact hx.1
        have hfin : Set.Finite (openInterval a b) := by
          rw [hempty]
          exact Set.finite_empty
        exact hInf hfin
  | union hA hB ihA ihB =>
      rename_i S T
      by_cases hSi : Set.Infinite S
      · obtain ⟨a, b, hlt, hsub⟩ := ihA hSi
        exact ⟨a, b, hlt, fun x hx => Or.inl (hsub x hx)⟩
      · have hSf : Set.Finite S := by
          by_contra hcon
          exact hSi hcon
        have hTinf : Set.Infinite T := by
          intro hTf
          apply hInf
          have hunion : (fun x : Power R 1 => S x ∨ T x) = S ∪ T := rfl
          rw [hunion]
          exact Set.Finite.union hSf hTf
        obtain ⟨a, b, hlt, hsub⟩ := ihB hTinf
        exact ⟨a, b, hlt, fun x hx => Or.inr (hsub x hx)⟩
