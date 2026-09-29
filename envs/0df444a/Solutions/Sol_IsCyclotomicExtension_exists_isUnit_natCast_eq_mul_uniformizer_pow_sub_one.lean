-- Prove2me | solution 1 for IsCyclotomicExtension.exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/694a195a-7224-50b0-af44-2780d7030303

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ u : Aˣ, (p : A) = ↑u * ϖ ^ (p - 1) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨z, hz⟩ := hζA

  have hzp : IsPrimitiveRoot z p := by
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap A L) ?_ (IsFractionRing.injective A L)
    rwa [hz]

  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {1 - z} :=
    IsDiscreteValuationRing.maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot p L ζ hζ A hAp z hz
  have hassocϖ : Associated (z - 1) ϖ := by
    have h1 : Associated (1 - z) ϖ := Ideal.span_singleton_eq_span_singleton.mp (hmax.symm.trans hϖ)
    have h2 : Associated (z - 1) (1 - z) := ⟨-1, by simp⟩
    exact h2.trans h1

  have hzp' : IsPrimitiveRoot z (p - 1 + 1) := by rwa [Nat.sub_add_cancel hp.one_le]
  have hprod := hzp'.prod_pow_sub_one_eq_order
  have hcast : ((p - 1 : ℕ) : A) + 1 = (p : A) := by
    rw [← Nat.cast_succ]
    exact congrArg (Nat.cast : ℕ → A) (Nat.succ_pred_eq_of_pos hp.pos)
  rw [hcast] at hprod

  have hfac : ∀ k, k ∈ Finset.range (p - 1) → Associated (z ^ (k + 1) - 1) (z - 1) := fun k hk => by
    refine (hzp.associated_sub_one_pow_sub_one_of_coprime ?_).symm
    have hk' : k + 1 < p := by have := Finset.mem_range.mp hk; omega
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hk'))
  have key : ∀ n, n ≤ p - 1 → Associated (∏ k ∈ Finset.range n, (z ^ (k + 1) - 1)) ((z - 1) ^ n) := by
    intro n hn
    induction n with
    | zero => simp only [Finset.range_zero, Finset.prod_empty, pow_zero]; exact Associated.refl 1
    | succ m ih =>
      rw [Finset.prod_range_succ, pow_succ (z - 1) m]
      exact (ih (by omega)).mul_mul (hfac m (Finset.mem_range.mpr (by omega)))
  have hpa : Associated (p : A) (∏ k ∈ Finset.range (p - 1), (z ^ (k + 1) - 1)) := by
    rw [← hprod]
    exact associated_unit_mul_left _ _ ((isUnit_one.neg).pow _)
  have H : Associated (p : A) (ϖ ^ (p - 1)) :=
    (hpa.trans (key (p - 1) le_rfl)).trans (hassocϖ.pow_pow)
  obtain ⟨u, hu⟩ := H.symm
  exact ⟨u, by rw [← hu, mul_comm]⟩

end S_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
end P2MW
export P2MW.S_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one (solution)
