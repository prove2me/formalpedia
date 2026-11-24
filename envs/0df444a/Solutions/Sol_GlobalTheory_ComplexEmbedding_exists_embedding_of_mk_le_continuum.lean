-- Prove2me | solution 1 for GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:55:55.490967+00:00
-- url     : https://prove2.me/submissions/c3647cd0-23f2-4dab-b4ee-69204d5bd758

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.ComplexEmbedding
open Cardinal IsLocalRing
namespace GlobalTheory.ComplexEmbedding
theorem _root_.solution {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (hΩ : #Ω ≤ 𝔠) (σ : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    simpa [Cardinal.mkRat] using this
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hst : #s ≤ #t := by
    have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK
      (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    rw [← h1, Cardinal.mk_complex]
    exact (Cardinal.mk_subtype_le _).trans hΩ
  obtain ⟨e⟩ := hst
  have hv : AlgebraicIndependent K (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let f : IntermediateField.adjoin K (Set.range ((↑) : s → Ω)) →ₐ[K] ℂ :=
    (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
  have halg := hs.isAlgebraic_field
  obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' f
    (fun (x : Ω) => ⟨(Algebra.IsAlgebraic.isAlgebraic
      (R := IntermediateField.adjoin K (Set.range ((↑) : s → Ω))) x).isIntegral, IsAlgClosed.splits _⟩)
  refine ⟨φ.toRingHom, ?_⟩
  ext x
  exact φ.commutes x
end GlobalTheory.ComplexEmbedding
