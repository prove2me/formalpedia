-- Prove2me | solution 1 for IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8ad7185a-c17c-5c03-b362-6ba8a35e21a2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped Pointwise

theorem KumS.eq_one_of_pow_eq_one_of_valuation_sub_one_lt {L : Type} [Field L] (A : ValuationSubring L) (p : ℕ)
    (hpA : A.valuation (p : L) = 1) (ζ : L) (hζA : A.valuation ζ ≤ 1) (hζp : ζ ^ p = 1) (hζ1 : A.valuation (ζ - 1) < 1) :
    ζ = 1 := by
  have hsum : A.valuation ((Finset.range p).sum (fun i => ζ ^ i) - (p : L)) < 1 := by
    have : (Finset.range p).sum (fun i => ζ ^ i) - (p : L) = (Finset.range p).sum (fun i => ζ ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [this]
    refine Valuation.map_sum_lt _ one_ne_zero (fun i _ => ?_)
    rw [← mul_geom_sum ζ i, Valuation.map_mul]
    have hcv : A.valuation ((Finset.range i).sum (fun j => ζ ^ j)) ≤ 1 :=
      Valuation.map_sum_le _ (fun j _ => by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le' hζA)
    calc A.valuation (ζ - 1) * A.valuation ((Finset.range i).sum (fun j => ζ ^ j))
        ≤ A.valuation (ζ - 1) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hζ1
  have hu : (Finset.range p).sum (fun i => ζ ^ i) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hpA] at hsum
    exact lt_irrefl _ hsum
  have hmul : (ζ - 1) * (Finset.range p).sum (fun i => ζ ^ i) = 0 := by rw [mul_geom_sum, hζp, sub_self]
  rcases mul_eq_zero.1 hmul with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hu

theorem KumS.valuation_sub_lt_one_of_mem_inertia {L : Type} [Field L] {K : Type} [Field K] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.inertiaSubgroupIn K) (a : L) (ha : a ∈ A) :
    A.valuation (σ a - a) < 1 := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ

  have hker : ∀ r : IsLocalRing.ResidueField A, τ • r = r := fun r => by
    have := MonoidHom.mem_ker.1 hτ
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) => f r) this
  have hres : IsLocalRing.residue A (τ • (⟨a, ha⟩ : A)) = IsLocalRing.residue A ⟨a, ha⟩ := by
    rw [IsLocalRing.ResidueField.residue_smul]
    exact hker _
  have hmem : τ • (⟨a, ha⟩ : A) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 hres
  have := (ValuationSubring.coe_mem_nonunits_iff).2 hmem
  rw [ValuationSubring.mem_nonunits_iff] at this
  exact this

theorem solution
    (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S)
    (x : AlgebraicClosure ℚ) (hxF : x ∈ F)
    (hxS : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) → x ∈ A ∧ x⁻¹ ∈ A)
    (α : AlgebraicClosure ℚ) (hα : α ^ (p : ℕ) = x) :
    (F ⊔ IntermediateField.adjoin ℚ {α}).IsUnramifiedOutside S := by
  classical
  obtain ⟨hfin, hF'⟩ := hF
  refine ⟨?_, fun q hq A hA σ hσ => ?_⟩
  · haveI := hfin
    have hint : IsIntegral ℚ α := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic α).isIntegral
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {α}) := IntermediateField.adjoin.finiteDimensional hint
    exact IntermediateField.finiteDimensional_sup _ _
  · have hσF : σ ∈ F.fixingSubgroup := hF' q hq A hA hσ

    have hσα : σ α = α := by
      have hp' : (p : ℕ).Prime := p.2
      have hq' : (q : ℕ).Prime := q.2
      have hpq : (p : ℕ) ≠ q := fun h => hq (by rwa [show p = q from Subtype.ext h] at hp)
      by_cases hx0 : x = 0
      · have : α = 0 := pow_eq_zero_iff hp'.ne_zero |>.1 (hα.trans hx0)
        rw [this, map_zero]
      have hα0 : α ≠ 0 := fun h => hx0 (by rw [← hα, h, zero_pow hp'.ne_zero])
      obtain ⟨hxA, hxA'⟩ := hxS q hq A hA
      let v := A.valuation

      have hvx : v x = 1 := by
        apply le_antisymm ((A.valuation_le_one_iff x).2 hxA)
        have h1 : v x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 hxA'
        rw [Valuation.map_inv, inv_le_one₀ ((Valuation.pos_iff _).2 hx0)] at h1
        exact h1
      have hvα : v α = 1 := by
        have hpow : v α ^ (p : ℕ) = 1 := by rw [← Valuation.map_pow, hα, hvx]
        rcases lt_trichotomy (v α) 1 with hlt | heq | hgt
        · exact absurd hpow (ne_of_lt (pow_lt_one₀ zero_le' hlt hp'.ne_zero))
        · exact heq
        · exact absurd hpow (ne_of_gt (one_lt_pow₀ hgt hp'.ne_zero))
      have hvq : v (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff _).1 hA
      have hvp : v ((p : ℕ) : AlgebraicClosure ℚ) = 1 := by
        apply le_antisymm (by exact_mod_cast (A.valuation_le_one_iff _).2 (natCast_mem A p))
        by_contra hlt
        push Not at hlt
        obtain ⟨a, b, hab⟩ := (Nat.coprime_primes hp' hq').2 hpq |>.isCoprime
        have h1 : v (1 : AlgebraicClosure ℚ) < 1 := by
          have : (1 : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ) * (p : ℕ) + (b : AlgebraicClosure ℚ) * (q : ℕ) := by
            exact_mod_cast congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hab.symm
          rw [this]
          refine Valuation.map_add_lt _ ?_ ?_
          · rw [Valuation.map_mul]
            calc v a * v ((p:ℕ) : AlgebraicClosure ℚ) ≤ 1 * v ((p:ℕ) : AlgebraicClosure ℚ) := by
                  gcongr; exact (A.valuation_le_one_iff _).2 (intCast_mem A a)
              _ < 1 := by rw [one_mul]; exact hlt
          · rw [Valuation.map_mul]
            calc v b * v ((q:ℕ) : AlgebraicClosure ℚ) ≤ 1 * v ((q:ℕ) : AlgebraicClosure ℚ) := by
                  gcongr; exact (A.valuation_le_one_iff _).2 (intCast_mem A b)
              _ < 1 := by rw [one_mul]; exact hvq
        rw [Valuation.map_one] at h1
        exact lt_irrefl _ h1

      have hσx : σ x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσF x hxF
      have hαA : α ∈ A := (A.valuation_le_one_iff α).1 hvα.le
      set ζ := σ α * α⁻¹ with hζ
      have hζp : ζ ^ (p : ℕ) = 1 := by
        rw [hζ, mul_pow, ← map_pow, hα, hσx, ← hα, ← mul_pow, mul_inv_cancel₀ hα0, one_pow]
      have hvσα : v (σ α) = 1 := by
        have hpow : v (σ α) ^ (p : ℕ) = 1 := by rw [← Valuation.map_pow, ← map_pow, hα, hσx, hvx]
        rcases lt_trichotomy (v (σ α)) 1 with hlt | heq | hgt
        · exact absurd hpow (ne_of_lt (pow_lt_one₀ zero_le' hlt hp'.ne_zero))
        · exact heq
        · exact absurd hpow (ne_of_gt (one_lt_pow₀ hgt hp'.ne_zero))
      have hζA : v ζ ≤ 1 := by rw [hζ, Valuation.map_mul, Valuation.map_inv, hvσα, hvα, inv_one, mul_one]
      have hζ1 : v (ζ - 1) < 1 := by
        have : ζ - 1 = (σ α - α) * α⁻¹ := by rw [hζ, sub_mul, mul_inv_cancel₀ hα0]
        rw [this, Valuation.map_mul, Valuation.map_inv, hvα, inv_one, mul_one]
        exact KumS.valuation_sub_lt_one_of_mem_inertia A σ hσ α hαA
      have hζone : ζ = 1 := KumS.eq_one_of_pow_eq_one_of_valuation_sub_one_lt A p hvp ζ hζA hζp hζ1
      have := congrArg (· * α) hζone
      simpa [hζ, mul_assoc, inv_mul_cancel₀ hα0] using this

    rw [IntermediateField.fixingSubgroup_sup]
    refine Subgroup.mem_inf.2 ⟨hσF, ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hle : IntermediateField.adjoin ℚ {α} ≤ IntermediateField.fixedField (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) α) := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      intro g
      exact g.2
    exact (hle hy) ⟨σ, hσα⟩

end S_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
end P2MW
export P2MW.S_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq (solution)
