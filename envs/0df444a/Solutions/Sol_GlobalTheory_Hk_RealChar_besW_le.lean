-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.besW_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:36.86266+00:00
-- url     : https://prove2.me/submissions/f0614743-72d4-408f-84df-fc4b4a98618b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_kerW_le
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
theorem _root_.solution : ∃ G : ℝ, 0 ≤ G ∧ ∀ y : ℝ, 0 < y → besW y ≤ G / y ^ 3 := by
  refine ⟨6 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-w) * w ^ ((3 : ℝ) - 1), ?_, fun y hy => ?_⟩
  · refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun w hw => ?_)
    have : 0 < w := hw
    positivity
  · calc besW y ≤ ∫ w in Set.Ioi (0 : ℝ), 6 / y ^ 3 * (Real.exp (-w) * w ^ ((3 : ℝ) - 1)) :=
          setIntegral_mono_on (integrableOn_kerW hy)
            ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3))
            measurableSet_Ioi fun w hw => kerW_le hy hw
      _ = _ := by rw [integral_const_mul]; ring
end GlobalTheory.Hk.RealChar
