-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.integrableOn_kerW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:07.852898+00:00
-- url     : https://prove2.me/submissions/91c9d7d5-7009-4de5-a105-8d2fe9b804e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_kerW_pos
import Theorems.Thm_GlobalTheory_Hk_RealChar_kerW_le
import Theorems.Thm_GlobalTheory_Hk_RealChar_measurable_kerW

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
theorem _root_.solution {y : ℝ} (hy : 0 < y) : IntegrableOn (kerW y) (Set.Ioi 0) := by
  refine Integrable.mono' ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3))
    (measurable_kerW y).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  rw [Real.norm_of_nonneg (kerW_pos y hw).le]
  exact kerW_le hy hw
end GlobalTheory.Hk.RealChar
