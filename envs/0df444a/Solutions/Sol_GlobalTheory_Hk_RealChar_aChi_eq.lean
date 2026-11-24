-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.aChi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:04.582577+00:00
-- url     : https://prove2.me/submissions/a39258e6-44eb-4b33-924d-dd752b02f654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_chi_real

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
theorem _root_.solution {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (n : ℕ) :
    𝓕.aChi χ n = (bRe 𝓕 χ n : ℂ) := by
  unfold LFam.aChi bRe
  push_cast
  refine Finset.sum_congr rfl fun g _ => ?_
  rcases chi_real h g with e | e <;> simp [e]
end GlobalTheory.Hk.RealChar
