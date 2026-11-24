-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.exists_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:47:41.157597+00:00
-- url     : https://prove2.me/submissions/2c1a2751-cb6c-4795-bce2-3f04edfcbcec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_chirpS_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_kerS_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_kerOp_three_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_integral_chirp_kerOp

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
theorem _root_.solution (C : ℂ) (k a : ℝ) (hC : C ≠ 0) (hk : k ≠ 0) (ha : a = 2 * |k|)
    (R : V ≃ₗᵢ[ℝ] V) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : 𝓢(V, ℂ),
      kerOp C a R (kerOp C a R (kerOp C a R (fun u => chirp k u *
        kerOp C a R (fun u => chirp k u * φ u) u))) 0 = c * ∫ v, φ v := by
  have ha0 : a ≠ 0 := by rw [ha]; have := abs_pos.2 hk; positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hb₀0 : (-(2 * Real.pi * k * I) : ℂ) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hkC) Complex.I_ne_zero)
  refine ⟨C ^ 3 * ((|((-a) ^ Module.finrank ℝ V)⁻¹| : ℝ) : ℂ) *
    (C * (Real.pi / (-(2 * Real.pi * k * I) : ℂ)) ^ (Module.finrank ℝ V / 2 : ℂ)), ?_, fun φ => ?_⟩
  · refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) ?_) (mul_ne_zero hC ?_)
    · have : |((-a) ^ Module.finrank ℝ V)⁻¹| ≠ 0 :=
        abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 ha0)))
      exact_mod_cast this
    · intro h
      rw [Complex.cpow_eq_zero_iff] at h
      exact div_ne_zero hpi hb₀0 h.1
  · have e0 : (fun u : V => chirp k u * φ u) = chirpS k φ := by
      funext u; rw [chirpS_apply]
    have e1 : (fun u : V => chirp k u * kerOp C a R (chirpS k φ) u) =
        chirpS k (kerS C a ha0 R (chirpS k φ)) := by
      funext u; rw [chirpS_apply, kerS_coe]
    rw [e0, e1, kerOp_three_zero C a ha0 R, ← e1, integral_chirp_kerOp C k a hk ha R φ]
    ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
