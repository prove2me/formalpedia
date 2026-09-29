-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_ringHom_adicCompletion_coeffSubring_valuationInteger
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/06e3eb91-69b8-5b23-ae6e-7cac971d36a9

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
import Theorems.Thm_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger

set_option autoImplicit false

open ModularCurve

open Valued in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)] :
    ∃ j : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion],
      ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ((o : AlgebraicClosure ℚ) : (A.valuation).Completion) := by
  classical

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥(NodeLocalized.coeffSubring A K)
  have hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hϖ0 : ϖ ≠ 0 := hϖirr.ne_zero

  obtain ⟨ιC, hιC, hvC⟩ : ∃ ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion,
      (∀ x, ιC x = (x : (A.valuation).Completion)) ∧ ∀ x, Valued.v (ιC x) = A.valuation x := by
    refine ⟨(UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* (A.valuation).Completion).comp
      (WithVal.equiv A.valuation).symm.toRingHom, fun x => rfl, fun x => ?_⟩
    show Valued.v (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : (A.valuation).Completion) = A.valuation x
    rw [Valued.valuedCompletion_apply]
    rfl

  have hϖA : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ∈ A := ϖ.2.1
  have hϖK : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ∈ K := ϖ.2.2
  have hϖ0' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hvϖ0 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    rwa [Valuation.ne_zero_iff]
  have hvϖ1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 := by
    refine lt_of_le_of_ne (A.valuation_le_one ⟨_, hϖA⟩) fun h1 => ?_

    have hinvA : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]
    have hinvK : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem hϖK
    have hunit : IsUnit ϖ := by
      refine ⟨⟨ϖ, ⟨_, ⟨hinvA, hinvK⟩⟩, Subtype.ext (mul_inv_cancel₀ hϖ0'), Subtype.ext (inv_mul_cancel₀ hϖ0')⟩, rfl⟩
    exact hϖirr.not_isUnit hunit

  have hOmem : ∀ x : AlgebraicClosure ℚ, A.valuation x ≤ 1 → ιC x ∈ 𝒪[(A.valuation).Completion] := fun x hx => by
    change Valued.v (ιC x) ≤ 1; rw [hvC]; exact hx
  obtain ⟨ϖC, hϖC⟩ : ∃ ϖC : 𝒪[(A.valuation).Completion],
      (ϖC : (A.valuation).Completion) = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) :=
    ⟨⟨ιC _, hOmem _ hvϖ1.le⟩, rfl⟩
  have hvϖC : Valued.v (ϖC : (A.valuation).Completion) = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [hϖC, hvC]
  have hϖC0 : (ϖC : (A.valuation).Completion) ≠ 0 := by
    rw [hϖC]; exact (map_ne_zero ιC).mpr hϖ0'
  haveI hAC : IsAdicComplete (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion] := by
    apply Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt ϖC hϖC0
    intro γ hγ
    rw [hvϖC]
    exact A.exists_valuation_pow_lt_of_isAlgebraic hvϖ0 hvϖ1 γ hγ

  have hmemO : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      (ιC.comp (NodeLocalized.coeffSubring A K).subtype) o ∈ 𝒪[(A.valuation).Completion] := fun o =>
    hOmem _ (A.valuation_le_one ⟨_, o.2.1⟩)
  let evO : ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion] := (ιC.comp (NodeLocalized.coeffSubring A K).subtype).codRestrict _ hmemO
  have hevOϖ : evO ϖ = ϖC := Subtype.ext (by rw [hϖC]; rfl)
  have hcontO : ∀ k' : ℕ, ∃ n : ℕ, IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) ^ n ≤ (Ideal.span {ϖC} ^ k').comap evO := by
    intro k'
    refine ⟨k', fun a ha => ?_⟩
    rw [hϖgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [Ideal.mem_comap, map_mul, map_pow, hevOϖ, Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (dvd_refl _))
  obtain ⟨j, hjcomp⟩ := AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
    (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) (Ideal.span {ϖC}) evO hcontO
  refine ⟨j, fun o => ?_⟩
  have : j (algebraMap _ _ o) = evO o := by rw [← RingHom.comp_apply, hjcomp]
  rw [this, ← hιC]
  rfl

end S_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger (solution)
