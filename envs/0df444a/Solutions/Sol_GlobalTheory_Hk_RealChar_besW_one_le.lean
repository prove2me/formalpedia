-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.besW_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:37.593266+00:00
-- url     : https://prove2.me/submissions/e9842adc-8ac5-4dd6-af9a-c73e9975b7db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_integrableOn_kerW

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
theorem _root_.solution {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : besW 1 ≤ besW v := by
  refine setIntegral_mono_on (integrableOn_kerW one_pos) (integrableOn_kerW hv)
    measurableSet_Ioi fun w hw => ?_
  have : 0 < w := hw
  unfold kerW
  gcongr
end GlobalTheory.Hk.RealChar
