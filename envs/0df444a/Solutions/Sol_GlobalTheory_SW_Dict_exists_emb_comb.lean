-- Prove2me | solution 1 for GlobalTheory.SW.Dict.exists_emb_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:51.573793+00:00
-- url     : https://prove2.me/submissions/ada06c07-ce30-44f3-9cff-7cc33898212b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution (c : Fin (Module.finrank ℚ E) → ℂ) :
    ∃ w : (E →+* ℂ) → ℂ, ∀ j, ∑ σ : E →+* ℂ, σ (Module.finBasis ℚ E j) * w σ = c j := by
  classical
  have hcard : Fintype.card (Fin (Module.finrank ℚ E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card]
  let e : Fin (Module.finrank ℚ E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let M := Algebra.embeddingsMatrixReindex ℚ ℂ (Module.finBasis ℚ E) e
  have hdet : M.det ≠ 0 := by
    intro h0
    have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (Module.finBasis ℚ E) e
    rw [h0, zero_pow two_ne_zero, map_eq_zero] at h
    exact Algebra.discr_not_zero_of_basis ℚ (Module.finBasis ℚ E) h
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))) c
  refine ⟨fun σ => v (e.symm (RingHom.equivRatAlgHom E ℂ σ)), fun j => ?_⟩
  rw [← hv]
  simp only [mulVec, dotProduct]
  refine Fintype.sum_equiv ((RingHom.equivRatAlgHom E ℂ).trans e.symm) _ _ fun σ => ?_
  simp [M, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
