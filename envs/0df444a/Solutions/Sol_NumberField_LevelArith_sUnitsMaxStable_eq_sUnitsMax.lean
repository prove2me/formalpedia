-- Prove2me | solution 1 for NumberField.LevelArith.sUnitsMaxStable_eq_sUnitsMax
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8d013623-8d32-540a-b3a7-6af1953ded22

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped TensorProduct Pointwise

namespace CycBaseInertia

lemma mem_inertiaSubgroupIn_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    g ∈ A.inertiaSubgroupIn ℚ ↔ g • A = A ∧ ∀ a ∈ A, g a - a ∈ A.nonunits := by
  constructor
  · intro hg
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨σ.2, fun a ha => ?_⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hσ
    have h2 := DFunLike.congr_fun hσ (IsLocalRing.residue A ⟨a, ha⟩)
    change σ • IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨a, ha⟩ at h2
    rw [← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue_def, IsLocalRing.residue_def] at h2
    exact ValuationSubring.coe_mem_nonunits_iff.mpr (Ideal.Quotient.eq.mp h2)
  · rintro ⟨h1, h2⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, h1⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change (⟨g, h1⟩ : A.decompositionSubgroup ℚ) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue_def, IsLocalRing.residue_def]
    exact Ideal.Quotient.eq.mpr (ValuationSubring.coe_mem_nonunits_iff.mp (h2 a a.2))

lemma smul_mem_nonunits_smul {A : ValuationSubring (AlgebraicClosure ℚ)} {y : AlgebraicClosure ℚ}
    (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hy : y ∈ A.nonunits) : x • y ∈ (x • A).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hy ⊢
  rcases hy with rfl | hy
  · left; exact smul_zero x
  · right
    rw [← smul_inv'', ValuationSubring.smul_mem_pointwise_smul_iff]; exact hy

lemma liesOverPrime_smul (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ)
    (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : A.LiesOverPrime q) : (x • A).LiesOverPrime q := by
  unfold ValuationSubring.LiesOverPrime at h ⊢
  have h' := smul_mem_nonunits_smul x h
  rwa [show x • (q : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) from map_natCast x q] at h'

lemma conj_mem_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ))
    (g x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hg : g ∈ A.inertiaSubgroupIn ℚ) :
    x * g * x⁻¹ ∈ (x • A).inertiaSubgroupIn ℚ := by
  rw [mem_inertiaSubgroupIn_iff] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, fun b hb => ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · obtain ⟨a, ha, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists x b A).mp hb
    have hcalc : (x * g * x⁻¹) (x • a) - x • a = x • (g a - a) := by
      show x (g (x⁻¹ (x a))) - x a = x (g a - a)
      rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply, map_sub]
    rw [hcalc]
    exact smul_mem_nonunits_smul x (h2 a ha)

lemma isUnramifiedOutside_map {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (F.map (γ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  refine ⟨inferInstance, fun q hq A hA σ hσ => ?_⟩

  have h1 : γ⁻¹ * σ * γ⁻¹⁻¹ ∈ (γ⁻¹ • A).inertiaSubgroupIn ℚ := conj_mem_inertiaSubgroupIn A σ γ⁻¹ hσ
  rw [inv_inv] at h1
  have h2 : γ⁻¹ * σ * γ ∈ F.fixingSubgroup := hF.2 q hq (γ⁻¹ • A) (liesOverPrime_smul A q γ⁻¹ hA) h1
  rw [IntermediateField.mem_fixingSubgroup_iff] at h2 ⊢
  rintro _ ⟨z, hz, rfl⟩
  have h3 := h2 z hz

  have h4 : σ (γ z) = γ ((γ⁻¹ * σ * γ) z) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  show σ (γ z) = γ z
  rw [h4, h3]

end CycBaseInertia

theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    sUnitsMaxStable S L = sUnitsMax S := by
  apply le_antisymm (sUnitsMaxStable_le S L)
  intro x hx
  rw [mem_sUnitsMaxStable_iff]
  intro γ
  obtain ⟨⟨F, hF, hxF⟩, hunit⟩ := hx
  refine ⟨⟨F.map ((γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ),
    CycBaseInertia.isUnramifiedOutside_map hF _, ⟨(x : AlgebraicClosure ℚ), hxF, rfl⟩⟩, fun q hq A hA => ?_⟩
  have hA' : ((γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)⁻¹ • A).LiesOverPrime (q : ℕ) := CycBaseInertia.liesOverPrime_smul A q _ hA
  obtain ⟨h1, h2⟩ := hunit q hq _ hA'
  constructor
  · show (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • (x : AlgebraicClosure ℚ) ∈ A
    rw [← smul_inv_smul (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) A, ValuationSubring.smul_mem_pointwise_smul_iff]
    exact h1
  · show (((γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • x)⁻¹ : (AlgebraicClosure ℚ)ˣ).val ∈ A
    rw [← smul_inv']
    show (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A
    rw [← smul_inv_smul (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) A, ValuationSubring.smul_mem_pointwise_smul_iff]
    exact h2

end S_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
end P2MW
export P2MW.S_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax (solution)
