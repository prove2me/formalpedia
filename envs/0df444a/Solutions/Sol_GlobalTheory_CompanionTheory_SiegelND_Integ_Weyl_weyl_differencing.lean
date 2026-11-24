-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_differencing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:44.545473+00:00
-- url     : https://prove2.me/submissions/1eef0cb2-ca16-427d-8d51-9de6fc871c49

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_fourier_diffS_decay
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_enorm_sq_le

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : SchwartzMap V ℂ) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : V → ℝ) (T : V →ₗ[ℝ] V), Continuous q →
      (∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) →
      ENNReal.ofReal (‖∫ x, f x * Complex.exp (2 * Real.pi * Complex.I * ((q x : ℝ) : ℂ))‖ ^ 2) ≤
        ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖T y‖) ^ K)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := fourier_diffS_decay f K
  refine ⟨C, hC0, fun q T hq hT => (enorm_sq_le f q T hq hT).trans ?_⟩
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hC0, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using hC y (-(T y))
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
