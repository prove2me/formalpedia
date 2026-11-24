-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.bRe_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:05.957773+00:00
-- url     : https://prove2.me/submissions/89e00dd3-7512-4dce-bfa5-7954b579e28a

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
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) : bRe 𝓕 χ 1 = 1 := by
  unfold bRe
  rw [Finset.sum_eq_single 0 (fun g _ hg => by simp [𝓕.a_one_ne g hg]) (by simp)]
  simp [𝓕.a_one]
end GlobalTheory.Hk.RealChar
