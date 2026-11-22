-- Prove2me | solution 1 for Monotonicity_Theorem.infinite_definable_set_contains_interval2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-14T23:49:01.14115+00:00
-- url     : https://prove2.me/submissions/183878ad-ff49-4755-bb0f-8389d7d26be6

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_contains_interval_core2

open Monotonicity_Theorem

-- An infinite definable set of unary tuples contains a nondegenerate open
-- interval: o-minimality turns definability into a finite-union structure,
-- and the interval core extracts the interval from infiniteness.
theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R) (I : Set (Power R 1)) (hDef : M.S 1 I) (hInf : Set.Infinite I) : ∃ a b : Endpoint R, Endpoint.lt a b ∧ (openInterval a b).Subset I := by
  obtain ⟨a, b, hlt, hsub⟩ :=
    Monotonicity_Theorem.infinite_contains_interval_core2 I ((M.ominimal I).mp hDef) hInf
  exact ⟨a, b, hlt, hsub⟩
