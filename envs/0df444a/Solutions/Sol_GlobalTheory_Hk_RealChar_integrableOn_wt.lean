-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.integrableOn_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:07.368859+00:00
-- url     : https://prove2.me/submissions/a232ac14-b7b2-4486-bd19-f6dc8b74d5ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_wt_nonneg

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
theorem _root_.solution : IntegrableOn wt (Set.Ioi 0) := by
  have hm : Measurable wt := by unfold wt; fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2)) (a := 0) (b := 1)
      (by norm_num)).1 hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)
    have h0 : 0 < w := hw.1
    rw [Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 h0
    unfold wt
    calc min w (1 / w) / (Real.sqrt w * w) ≤ w / (Real.sqrt w * w) := by
          gcongr; exact min_le_left _ _
      _ = _ := by field_simp
  · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos)
      hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    have h1 : 1 < w := hw
    have h0 : 0 < w := by linarith
    rw [Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, Real.rpow_two]
    have hs : 1 ≤ Real.sqrt w := Real.one_le_sqrt.2 h1.le
    unfold wt
    calc min w (1 / w) / (Real.sqrt w * w) ≤ (1 / w) / (1 * w) := by
          gcongr; exact min_le_right _ _
      _ = _ := by field_simp
end GlobalTheory.Hk.RealChar
