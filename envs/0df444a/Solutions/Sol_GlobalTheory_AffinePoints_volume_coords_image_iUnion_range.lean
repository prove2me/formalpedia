-- Prove2me | solution 1 for GlobalTheory.AffinePoints.volume_coords_image_iUnion_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:09.148826+00:00
-- url     : https://prove2.me/submissions/9afc9a9e-a795-440f-84b2-77edefea5aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_volume_range_eq_zero_of_mdifferentiable
import Theorems.Thm_GlobalTheory_AffinePoints_mdifferentiableAt_pi_of_forall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
variable {ι : Type*} [Countable ι] {E H M : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℂ (E i) (H i)} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hE : ∀ i, finrank ℂ (E i) < d) (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ))
    (hφ : ∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) :
    volume (coords g '' ⋃ i, range (φ i)) = 0 := by
  rw [image_iUnion]
  refine measure_iUnion_null fun i => ?_
  rw [← range_comp]
  exact volume_range_eq_zero_of_mdifferentiable (I := I i) (hE i) fun m =>
    mdifferentiableAt_pi_of_forall fun j => hφ i _ m
end GlobalTheory.AffinePoints
