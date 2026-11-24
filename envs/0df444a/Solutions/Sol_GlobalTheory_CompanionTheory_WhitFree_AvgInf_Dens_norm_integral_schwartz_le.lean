-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.norm_integral_schwartz_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:44.661205+00:00
-- url     : https://prove2.me/submissions/ef7c78a0-5837-4e98-80a5-f01fe7b58353

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_norm_fourier_le
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_integral_schwartz_eq

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
theorem _root_.solution (m : Measure V) [IsFiniteMeasure m] (hi : Integrable (chf m)) (g : 𝓢(V, ℂ)) :
    ‖∫ y, g y ∂m‖ ≤ (∫ x, ‖g x‖) * ∫ ξ, ‖chf m ξ‖ := by
  rw [integral_schwartz_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hi.norm.const_mul _)
    (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_fourier_le g ξ) (norm_nonneg _)
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
