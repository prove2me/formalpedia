-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.seminorm_diffS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:47.206335+00:00
-- url     : https://prove2.me/submissions/94702745-9883-4549-af6d-22d0cf1c5135

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
theorem _root_.solution (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ k n (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := diffFun_bound f k n K
  refine ⟨C, hC0, fun y => ?_⟩
  have hy : 0 < (1 + ‖y‖) ^ K := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  rw [← div_eq_mul_inv, le_div_iff₀ hy]
  exact hC x y
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
