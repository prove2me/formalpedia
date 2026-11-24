-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.kerOp_eq_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:18.829321+00:00
-- url     : https://prove2.me/submissions/ba3b5905-d27d-473b-a0bf-7a5ef3a6aa74

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_scaleEquiv_apply

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
theorem _root_.solution (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (g : V → ℂ) (u : V) :
    kerOp C a R g u = C * 𝓕 g (scaleEquiv a ha R u) := by
  rw [Real.fourier_eq', kerOp]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h : ⟪u, R v⟫ = ⟪R.symm u, v⟫ := by
    rw [← R.inner_map_map (R.symm u) v, R.apply_symm_apply]
  simp only [scaleEquiv_apply, inner_smul_right, smul_eq_mul, h, real_inner_comm]
  congr 2
  push_cast
  ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
