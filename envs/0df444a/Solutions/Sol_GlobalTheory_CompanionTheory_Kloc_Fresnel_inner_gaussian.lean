-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.inner_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:53.940662+00:00
-- url     : https://prove2.me/submissions/14992950-786c-45ed-a14e-9349c6745199

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) {b : ℂ} (hb : 0 < b.re) (v : V) :
    ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) =
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb (2 * Real.pi * I * a) (R v)
  rw [R.norm_map] at h
  have hb0 : b ≠ 0 := by contrapose! hb; simp [hb]
  convert h using 2
  · funext t
    rw [← Complex.exp_add]
    congr 1
    rw [real_inner_comm]
    push_cast
    ring
  · congr 1
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
