-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:33.457809+00:00
-- url     : https://prove2.me/submissions/7b423d1d-6fcd-4fac-b7fb-6556e3f5547d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (b₂ : Module.Basis (Fin 2) F E) (Δ : F), Δ ≠ 0 ∧ b₂ 0 = 1 ∧
      b₂ 1 * b₂ 1 = algebraMap F E Δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv (x : E) : σ (σ x) = x := by
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra! hc
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have h' := h.2.2.2 τ x
    rw [hc] at h'
    simpa using h'.symm
  set δ : E := x - σ x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσ : σ δ = -δ := by rw [hδ, map_sub, hinv, neg_sub]
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have h2 := congrArg σ hst
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσ, map_zero] at h2
    have hs2 : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hst + h2
    have hs : s = 0 :=
      (mul_eq_zero.1 ((map_eq_zero_iff _ (algebraMap F E).injective).1 hs2)).resolve_left
        two_ne_zero
    refine ⟨hs, ?_⟩
    rw [hs, map_zero, zero_add] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 ((mul_eq_zero.1 hst).resolve_right hδ0)
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.2.2.1]
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard with hB
  have hB0 : B 0 = 1 := by simp [hB]
  have hB1 : B 1 = δ := by simp [hB]
  obtain ⟨α, β, hs⟩ : ∃ α β : F, δ * δ = algebraMap F E α + algebraMap F E β * δ := by
    have hs := (B.sum_repr (δ * δ)).symm
    rw [Fin.sum_univ_two, hB0, hB1, Algebra.smul_def, Algebra.smul_def, mul_one] at hs
    exact ⟨_, _, hs⟩
  have h2 := congrArg σ hs
  rw [map_mul, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσ] at h2
  have hc : algebraMap F E β = 0 := by
    have : (2 * δ) * algebraMap F E β = 0 := by
      linear_combination h2 - hs
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hδ0)
  rw [hc, zero_mul, add_zero] at hs
  refine ⟨B, α, ?_, hB0, by rw [hB1]; exact hs⟩
  intro h0
  rw [h0, map_zero] at hs
  exact mul_self_ne_zero.2 hδ0 hs
end GlobalTheory.CompanionTheory.SW.PrimGood
