-- Prove2me | solution 1 for GlobalTheory.AffinePoints.iUnion_range_ne_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:49.796399+00:00
-- url     : https://prove2.me/submissions/7a3f813e-8700-48ac-bad0-6777ec7e432c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_exists_finite_injective_of_ringKrullDim_eq
import Theorems.Thm_GlobalTheory_AffinePoints_surjective_coords
import Theorems.Thm_GlobalTheory_AffinePoints_volume_coords_image_iUnion_range

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
theorem _root_.solution [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hE : ∀ i, finrank ℂ (E i) < d) (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ))
    (hφ : ∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) : ⋃ i, range (φ i) ≠ univ := by
  obtain ⟨g, hinj, hg⟩ := exists_finite_injective_of_ringKrullDim_eq (K := ℂ) hd
  intro h
  have := volume_coords_image_iUnion_range g hE φ hφ
  rw [h, image_univ, (surjective_coords g hg hinj).range_eq] at this
  exact (isOpen_univ.measure_ne_zero volume univ_nonempty) this
end GlobalTheory.AffinePoints
