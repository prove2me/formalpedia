-- Prove2me | solution 1 for GlobalTheory.AffinePoints.complexPoints_manifold_and_dimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:18.806076+00:00
-- url     : https://prove2.me/submissions/9fe14e7b-5042-4f87-b8e0-38acd54cdd9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_volume_coords_image_zeroSet_of_etale
import Theorems.Thm_GlobalTheory_AffinePoints_interior_zeroSet_eq_empty
import Theorems.Thm_GlobalTheory_AffinePoints_IsAlgebraicChart_volume_image_zeroSet
import Theorems.Thm_GlobalTheory_AffinePoints_iUnion_range_ne_univ
import Theorems.Thm_GlobalTheory_AffinePoints_dense_compl_iUnion_range
import Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_contMDiff_eval
import Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_isManifold
import Theorems.Thm_GlobalTheory_AffinePoints_exists_chart_of_etale
import Theorems.Thm_GlobalTheory_AffinePoints_hasAlgebraicCharts_of_isStandardSmooth
import Theorems.Thm_GlobalTheory_AffinePoints_isLocalHomeomorph_coords_of_etale


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
namespace GlobalTheory.AffinePoints
theorem _root_.solution (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (d : ℕ) :
    (∀ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale →
      IsLocalHomeomorph (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) ∧
      ∀ p : A →ₐ[ℂ] ℂ, ∃ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), p ∈ e.source ∧
        (e : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) = coords g ∧
        ∀ a, AnalyticOnNhd ℂ (fun z => e.symm z a) e.target) ∧
    (Algebra.IsStandardSmoothOfRelativeDimension d ℂ A →
      (∃ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale) ∧
      ∃ h : HasAlgebraicCharts ℂ A d,
        letI := h.chartedSpace
        IsManifold 𝓘(ℂ, Fin d → ℂ) ω (A →ₐ[ℂ] ℂ) ∧
          ∀ a : A, ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω fun p : A →ₐ[ℂ] ℂ => p a) ∧
    (IsDomain A → ringKrullDim A = d →
      (∀ f : A, f ≠ 0 →
        IsClosed {p : A →ₐ[ℂ] ℂ | p f = 0} ∧ interior {p : A →ₐ[ℂ] ℂ | p f = 0} = ∅ ∧
        (∀ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale →
          volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0) ∧
        ∀ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), IsAlgebraicChart e →
          volume (e '' (e.source ∩ {p | p f = 0})) = 0) ∧
      ∀ (ι : Type) [Countable ι] (E H M : ι → Type) [∀ i, NormedAddCommGroup (E i)]
        [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
        (I : ∀ i, ModelWithCorners ℂ (E i) (H i)) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]
        (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ)), (∀ i, finrank ℂ (E i) < d) →
        (∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) →
        ⋃ i, range (φ i) ≠ univ ∧ Dense (⋃ i, range (φ i))ᶜ) := by
  refine ⟨fun g hg => ⟨isLocalHomeomorph_coords_of_etale g hg, exists_chart_of_etale g hg⟩,
    fun _ => ⟨Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d ℂ A,
      hasAlgebraicCharts_of_isStandardSmooth, HasAlgebraicCharts.isManifold _,
      HasAlgebraicCharts.contMDiff_eval _⟩,
    fun _ hd => ⟨fun f hf => ⟨isClosed_zeroSet f, interior_zeroSet_eq_empty hf,
      fun g hg => volume_coords_image_zeroSet_of_etale g hg hf,
      fun e he => he.volume_image_zeroSet hd hf⟩, ?_⟩⟩
  intro ι _ E H M _ _ _ _ I _ _ _ _ φ hE hφ
  exact ⟨iUnion_range_ne_univ hd hE φ hφ, dense_compl_iUnion_range hd hE φ hφ⟩
end GlobalTheory.AffinePoints
