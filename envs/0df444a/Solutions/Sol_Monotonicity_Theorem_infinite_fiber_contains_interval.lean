-- Prove2me | solution 1 for Monotonicity_Theorem.infinite_fiber_contains_interval
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:59:11.139075+00:00
-- url     : https://prove2.me/submissions/20f96f3e-d289-469f-9d91-ec6c20867451

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval
open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) (A : Set (Power R 1))
    (hDef : M.S 1 A) (hInf : IsInfinite1 A) :
    exists a b : Endpoint R, Endpoint.lt D a b /\
      (openInterval D a b).Subset A := by
  exact Monotonicity_Theorem.infinite_definable_set_contains_interval D M A hDef hInf