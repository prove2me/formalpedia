-- Prove2me | solution 1 for IntermediateField.IsUnramifiedOutside.sup_adjoin_simple_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b574fb8d-0241-5240-8339-5a7be4d59711

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem

set_option autoImplicit false
set_option linter.unusedSectionVars false

local instance isAlgebraicQbar_kf : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

namespace P2MKfield

open ValuationSubring
open scoped Pointwise

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma val_mul_lt_one (A : ValuationSubring ℚb) {x y : ℚb} (hx : A.valuation x ≤ 1) (hy : A.valuation y < 1) :
    A.valuation (x * y) < 1 := by
  rw [map_mul]
  exact (mul_le_of_le_one_left' hx).trans_lt hy

lemma not_liesOverPrime_of_ne (A : ValuationSubring ℚb) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hne : q ≠ q')
    (h : A.LiesOverPrime q) : ¬ A.LiesOverPrime q' := by
  intro h'
  obtain ⟨a, b, hab⟩ := ((Nat.coprime_primes hq hq').2 hne).isCoprime
  have hab' : (a : ℚb) * q + (b : ℚb) * q' = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚb)) hab
  have hlt : A.valuation ((a : ℚb) * q + (b : ℚb) * q') < 1 :=
    Valuation.map_add_lt _ (val_mul_lt_one A ((A.valuation_le_one_iff _).2 (intCast_mem A a)) h)
      (val_mul_lt_one A ((A.valuation_le_one_iff _).2 (intCast_mem A b)) h')
  rw [hab', map_one] at hlt
  exact lt_irrefl _ hlt

lemma val_sub_lt_one_of_mem_inertia (A : ValuationSubring ℚb) {σ : Γ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {a : ℚb}
    (ha : a ∈ A) : A.valuation (σ a - a) < 1 := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
  have h1 := RingEquiv.congr_fun hτ (IsLocalRing.residue A ⟨a, ha⟩)
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply, RingAut.one_apply,
    ← IsLocalRing.ResidueField.residue_smul] at h1
  have h1' : τ • (⟨a, ha⟩ : A) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 h1
  exact (A.coe_mem_nonunits_iff).2 h1'

lemma smul_mem_of_mem_inertia (A : ValuationSubring ℚb) {σ : Γ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {a : ℚb} (ha : a ∈ A) :
    σ a ∈ A := by
  obtain ⟨τ, _, rfl⟩ := Subgroup.mem_map.1 hσ
  have hτA : (τ : Γ) • A = A := τ.2
  have : (τ : Γ) • a ∈ (τ : Γ) • A := smul_mem_pointwise_smul _ _ _ ha
  rw [hτA] at this
  exact this

lemma mem_fixingSubgroup_adjoin_of_apply_eq {σ : Γ} {α : ℚb} (h : σ α = α) :
    σ ∈ (IntermediateField.adjoin ℚ {α}).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : IntermediateField.adjoin ℚ {α} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer Γ α := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]; exact h
    exact hst hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)

end P2MKfield

open P2MKfield in
theorem solution
    (S : Finset Nat.Primes) {p : ℕ} (hp : p.Prime) (hpS : (⟨p, hp⟩ : Nat.Primes) ∈ S)
    {F : IntermediateField ℚ (AlgebraicClosure ℚ)} (hF : F.IsUnramifiedOutside S)
    {α : AlgebraicClosure ℚ} (hα : α ^ p ∈ F)
    (hαS : ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
      α ^ p ∈ A ∧ (α ^ p)⁻¹ ∈ A) :
    (F ⊔ IntermediateField.adjoin ℚ {α}).IsUnramifiedOutside S := by
  haveI := hF.1
  refine ⟨?_, fun q hq A hA σ hσ => ?_⟩
  ·
    have h1 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {α}) := by
      have := IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α).isIntegral)
      convert this
    have := @IntermediateField.finiteDimensional_sup ℚ (AlgebraicClosure ℚ) _ _ _ F (IntermediateField.adjoin ℚ {α})
      (by convert hF.1) (by convert h1)
    convert this
  · rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    have hσF : σ ∈ F.fixingSubgroup := hF.2 q hq A hA hσ
    refine ⟨hσF, mem_fixingSubgroup_adjoin_of_apply_eq ?_⟩

    have hAS : ∀ q' ∈ S, ¬ A.LiesOverPrime ((q' : Nat.Primes) : ℕ) := by
      intro q' hq'S
      refine not_liesOverPrime_of_ne A q.2 q'.2 (fun h => hq ?_) hA
      have : q = q' := Subtype.ext h
      rwa [this]
    have hAp : ¬ A.LiesOverPrime p := hAS ⟨p, hp⟩ hpS
    obtain ⟨huA, huA'⟩ := hαS A hAS
    have hσu : σ (α ^ p) = α ^ p := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσF _ hα
    by_cases hα0 : α = 0
    · rw [hα0, map_zero]

    have hp0 : p ≠ 0 := hp.ne_zero
    have hvα : A.valuation α = 1 := by
      have hu1 : A.valuation (α ^ p) ≤ 1 := (A.valuation_le_one_iff _).2 huA
      have hu2 : A.valuation (α ^ p)⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 huA'
      have hu0 : A.valuation (α ^ p) ≠ 0 := by
        rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hα0
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hu0)] at hu2
      have hu : A.valuation (α ^ p) = 1 := le_antisymm hu1 hu2
      rw [map_pow] at hu
      rcases lt_trichotomy (A.valuation α) 1 with h | h | h
      · exact absurd hu (pow_lt_one₀ zero_le' h hp0).ne
      · exact h
      · exact absurd hu (one_lt_pow₀ h hp0).ne'
    have hαA : α ∈ A := (A.valuation_le_one_iff _).1 hvα.le
    have hαA' : α⁻¹ ∈ A := (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hvα, inv_one])

    set ξ : AlgebraicClosure ℚ := σ α * α⁻¹ with hξ
    have hσα : σ α = ξ * α := by rw [hξ, inv_mul_cancel_right₀ hα0]
    have hξp : ξ ^ p = 1 := by
      rw [hξ, mul_pow, ← map_pow, hσu, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hα0)]
    have hξA : ξ ∈ A := A.mul_mem _ _ (smul_mem_of_mem_inertia A hσ hαA) hαA'
    have hvξ : A.valuation ξ ≤ 1 := (A.valuation_le_one_iff _).2 hξA

    have hv1 : A.valuation (ξ - 1) < 1 := by
      have h := val_sub_lt_one_of_mem_inertia A hσ hαA
      rw [hσα, ← sub_one_mul, map_mul, hvα, mul_one] at h
      exact h

    have hvi : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1 := by
      intro i
      rw [← geom_sum_mul, map_mul]
      refine (mul_le_of_le_one_left' ?_).trans_lt hv1
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_pow]; exact pow_le_one₀ zero_le' hvξ

    have hs : (∑ i ∈ Finset.range p, ξ ^ i) ≠ 0 := by
      intro hs0
      have hlt : A.valuation (∑ i ∈ Finset.range p, (ξ ^ i - 1)) < 1 :=
        Valuation.map_sum_lt _ one_ne_zero fun i _ => hvi i
      rw [Finset.sum_sub_distrib, hs0, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg,
        nsmul_eq_mul, mul_one] at hlt
      exact hAp hlt

    have hzero : (∑ i ∈ Finset.range p, ξ ^ i) * (ξ - 1) = 0 := by rw [geom_sum_mul, hξp, sub_self]
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h hs
    · rw [sub_eq_zero] at h
      rw [hσα, h, one_mul]

end S_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem
end P2MW
export P2MW.S_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem (solution)
