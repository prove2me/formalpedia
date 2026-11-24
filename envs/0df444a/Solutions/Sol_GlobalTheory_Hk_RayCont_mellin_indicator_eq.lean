-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.mellin_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:15.351151+00:00
-- url     : https://prove2.me/submissions/ead95b45-e6b9-4d51-985d-cb914d54b394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable {E : ℝ → ℂ} {C : ℝ}
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution (E : ℝ → ℂ) (s : ℂ) :
    mellin ((Set.Ioi (1 : ℝ)).indicator E) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ioi (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans (Set.mem_Ioi.1 ht)))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul, Set.indicator_of_mem ht]
    rw [mul_comm]
  · intro t ht
    rw [Set.indicator_of_notMem ht.2, smul_zero]
end GlobalTheory.Hk.RayCont
