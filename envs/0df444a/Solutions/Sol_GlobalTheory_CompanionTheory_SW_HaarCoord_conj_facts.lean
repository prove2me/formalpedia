-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:44.355962+00:00
-- url     : https://prove2.me/submissions/45d5b56d-9bab-4d2e-bda3-16141ce29acc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    (∀ x, σ (σ x) = x) ∧ ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, htc, -, hτ⟩ := h
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x =>
    v.embedding.injective (by rw [hτ, hτ, star_star])
  refine ⟨hinv, ?_⟩
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    have hc : ¬ ComplexEmbedding.IsReal v.embedding :=
      InfinitePlace.isComplex_iff.mp (htc.isComplex v)
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ v.embedding x
    rw [hall] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv]
  ring
end GlobalTheory.CompanionTheory.SW.HaarCoord
