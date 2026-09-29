-- Prove2me | solution 1 for IsDiscreteValuationRing.ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7143d82b-4b15-53ad-a136-a3b3df5f7249

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem solution
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    [PerfectRing (ResidueField W₀) q]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (f g : W₀ →+* T) [IsLocalHom f] [IsLocalHom g]
    (hfg : (residue T).comp f = (residue T).comp g) :
    f = g := by
  classical
  set 𝔪 := maximalIdeal T with h𝔪

  have hqW : ((q : ℕ) : W₀) ∈ IsLocalRing.maximalIdeal W₀ := by
    rw [hW₀]; exact Ideal.subset_span (Set.mem_singleton _)
  have hqT : ((q : ℕ) : T) ∈ 𝔪 := by
    rw [h𝔪, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (f ((q : ℕ) : W₀)) := by rwa [map_natCast]
    exact ((IsLocalRing.mem_maximalIdeal _).mp hqW) (IsLocalHom.map_nonunit _ hu')

  have hdecomp : ∀ x : W₀, ∃ y z : W₀, x = y ^ q + (q : W₀) * z := by
    intro x
    obtain ⟨ybar, hy⟩ := (PerfectRing.bijective_frobenius (R := ResidueField W₀) (p := q)).2 (residue W₀ x)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
    have hmem : x - y ^ q ∈ IsLocalRing.maximalIdeal W₀ := by
      rw [← Ideal.Quotient.eq]
      change residue W₀ x = residue W₀ (y ^ q)
      rw [map_pow]; exact hy.symm
    rw [hW₀, Ideal.mem_span_singleton'] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨y, z, by linear_combination -hz⟩

  have hbase : ∀ x : W₀, f x - g x ∈ 𝔪 := by
    intro x
    rw [h𝔪, ← Ideal.Quotient.eq]
    exact congrFun (congrArg DFunLike.coe hfg) x

  have hstep : ∀ n : ℕ, (∀ x : W₀, f x - g x ∈ 𝔪 ^ (n + 1)) := by
    intro n
    induction n with
    | zero => intro x; rw [pow_one]; exact hbase x
    | succ n ih =>
      intro x
      obtain ⟨y, z, rfl⟩ := hdecomp x
      rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
      have hS : (∑ i ∈ Finset.range q, (f y) ^ i * (g y) ^ (q - 1 - i)) ∈ 𝔪 := by
        rw [h𝔪, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        have hfy : Ideal.Quotient.mk (maximalIdeal T) (f y) = Ideal.Quotient.mk (maximalIdeal T) (g y) :=
          (Ideal.Quotient.eq).mpr (hbase y)
        simp_rw [map_mul, map_pow, hfy, ← pow_add]
        have : ∀ i ∈ Finset.range q, (Ideal.Quotient.mk (maximalIdeal T) (g y)) ^ (i + (q - 1 - i))
            = (Ideal.Quotient.mk (maximalIdeal T) (g y)) ^ (q - 1) := by
          intro i hi; congr 1; have := Finset.mem_range.mp hi; omega
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show ((q : ℕ) : T ⧸ maximalIdeal T) = 0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hqT, zero_mul]
      have hpow : (f y) ^ q - (g y) ^ q ∈ 𝔪 ^ (n + 1 + 1) := by
        rw [← Commute.geom_sum₂_mul (Commute.all _ _), pow_succ']
        exact Ideal.mul_mem_mul hS (ih y)
      have hqz : ((q : ℕ) : T) * f z - ((q : ℕ) : T) * g z ∈ 𝔪 ^ (n + 1 + 1) := by
        rw [← mul_sub, pow_succ']
        exact Ideal.mul_mem_mul hqT (ih z)
      have : f y ^ q + ((q : ℕ) : T) * f z - (g y ^ q + ((q : ℕ) : T) * g z)
          = (f y ^ q - g y ^ q) + (((q : ℕ) : T) * f z - ((q : ℕ) : T) * g z) := by ring
      rw [this]
      exact Ideal.add_mem _ hpow hqz

  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  refine RingHom.ext fun x => ?_
  have hx : f x - g x ∈ 𝔪 ^ N := Ideal.pow_le_pow_right (Nat.le_succ N) (hstep N x)
  rw [h𝔪, hN, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hx
  exact hx

end S_IsDiscreteValuationRing_ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast
end P2MW
export P2MW.S_IsDiscreteValuationRing_ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast (solution)
