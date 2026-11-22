-- Prove2me | solution 1 for Monotonicity_Theorem.infinite_definable_set_contains_interval
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:56:18.238917+00:00
-- url     : https://prove2.me/submissions/9cdafd1a-28b3-410b-939e-bfad79a86f9e

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_infinite_contains_interval_core
open Monotonicity_Theorem
set_option autoImplicit false

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R) (M : OMinimalStructure D) (I : Set (Power R 1)) (hDef : M.S 1 I) (hInf : IsInfinite1 I) : ∃ a b : Endpoint R, Endpoint.lt D a b ∧ (openInterval D a b).Subset I := by
  exact Monotonicity_Theorem.infinite_contains_interval_core D I ((M.ominimal I).mp hDef) hInf