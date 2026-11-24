-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.kerOp_three_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:30.349206+00:00
-- url     : https://prove2.me/submissions/ebabc5c8-fe60-43db-bcd7-1f5b3380ac9b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_scaleEquiv_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_kerOp_eq_fourier
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_kerS_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_kerOp_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_integral_fourier_schwartz

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
theorem _root_.solution (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (h : 𝓢(V, ℂ)) :
    kerOp C a R (kerOp C a R (kerOp C a R h)) 0 =
      C ^ 3 * ((|((-a) ^ Module.finrank ℝ V)⁻¹| : ℝ) : ℂ) * ∫ v, h v := by
  have e1 : kerOp C a R h = kerS C a ha R h := (kerS_coe C a ha R h).symm
  rw [kerOp_zero, e1]
  have e2 : (fun v => kerOp C a R (kerS C a ha R h) v) =
      fun v => C * 𝓕 (kerS C a ha R h : V → ℂ) ((-a) • R.symm v) := by
    funext v
    rw [kerOp_eq_fourier C a ha R, scaleEquiv_apply]
  rw [e2, integral_const_mul,
    R.symm.measurePreserving.integral_comp R.symm.toHomeomorph.measurableEmbedding
      (fun w => 𝓕 (kerS C a ha R h : V → ℂ) ((-a) • w)),
    Measure.integral_comp_smul, integral_fourier_schwartz, kerS_coe, kerOp_zero, Complex.real_smul]
  ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
