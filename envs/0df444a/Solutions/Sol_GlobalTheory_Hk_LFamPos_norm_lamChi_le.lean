-- Prove2me | solution 1 for GlobalTheory.Hk.LFamPos.norm_lamChi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:30:43.203829+00:00
-- url     : https://prove2.me/submissions/8ed74cda-21bb-48a8-a5a6-ff08fc39aec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivity

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LFamPos
namespace GlobalTheory.Hk.LFamPos
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]
end GlobalTheory.Hk.LFamPos
