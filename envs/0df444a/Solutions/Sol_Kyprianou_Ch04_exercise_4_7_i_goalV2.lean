-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_7_i_goalV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:36:06.623901+00:00
-- url     : https://prove2.me/submissions/042ca8e9-e49f-4d1f-a92b-d8512293dd8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_trueMartingale_deterministicLocalisation
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Theorems.Thm_Kyprianou_Ch04_kw47_trueMartingale_productGrid
import Theorems.Thm_Kyprianou_Ch04_kw47_signed_productGrid_integral
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open Kyprianou.Ch04
set_option autoImplicit false

theorem solution : certificate_ex4_7_i := by
  intro Omega inst P F L alpha hAlpha supX E H M
  haveI : IsProbabilityMeasure P := L.isProbability
  have hM : Martingale M F P := kw47_trueMartingale_productGrid P F L alpha hAlpha
  refine ⟨fun t w => M 0 w - M t w,
    kw47_signed_productGrid_integral P F L alpha hAlpha,
    Filter.Eventually.of_forall (fun w t => by ring),
    kw47_trueMartingale_deterministicLocalisation P F M hM⟩
