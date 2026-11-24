-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.schwartz_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:56:09.108566+00:00
-- url     : https://prove2.me/submissions/ccc2472a-a9c0-417b-9d94-4eecf1160397

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WhitFree.AvgInf GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
theorem _root_.solution (g : 𝓢(V, ℂ)) (y : V) :
    g y = ∫ ξ, Complex.exp (2 * π * I * ((⟪y, ξ⟫ : ℝ) : ℂ)) * (𝓕 g) ξ := by
  have h : (𝓕⁻ (𝓕 g)) y = g y := by rw [FourierTransform.fourierInv_fourier_eq]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  congr 2
  rw [real_inner_comm]
  push_cast
  ring
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
