-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.integrableOn_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:06.600484+00:00
-- url     : https://prove2.me/submissions/b17a6ed1-4dce-4922-99d6-9e9c3dd66117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

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
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {Q : ℝ → ℝ} (hm : Measurable Q) {E E' : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 1 ≤ t → |Q t| ≤ E' * Real.exp (-(t / 2))) : IntegrableOn Q (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ => E) (integrableOn_const (by simp)) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)
    refine (h1 w hw.1).trans ?_
    exact mul_le_of_le_one_right hE ((min_le_left _ _).trans hw.2)
  · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 (b := 1 / 2) (by norm_num)).const_mul E')
      hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    refine (h2 w (le_of_lt hw)).trans (le_of_eq ?_)
    congr 2; ring
end GlobalTheory.Hk.RealChar
