-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.besW_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:38.254613+00:00
-- url     : https://prove2.me/submissions/39429b7c-4213-41d6-8f57-93cc49221301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_kerW_pos
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
theorem _root_.solution : 0 < besW 1 := by
  unfold besW
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_kerW one_pos)]
  · have : Function.support (kerW 1) ∩ Set.Ioi 0 = Set.Ioi 0 :=
      Set.inter_eq_right.2 fun w hw => (kerW_pos 1 hw).ne'
    rw [this]; simp
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => (kerW_pos 1 hw).le)
end GlobalTheory.Hk.RealChar
