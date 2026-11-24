-- Prove2me | solution 1 for GlobalTheory.norm_ratCast_eq_padicNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:18.377968+00:00
-- url     : https://prove2.me/submissions/2c9158c6-9140-4c57-b93e-1eb9703a97fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
    (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (q : ℚ) :
    ‖(q : C)‖ = ‖(q : ℚ_[p])‖ := by
  have hlt : ‖(p : C)‖ < 1 := by
    rw [h]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hcop : ∀ m : ℕ, ¬ p ∣ m → ‖(m : C)‖ = 1 := by
    intro m hm
    refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C m) (not_lt.1 fun hm1 => ?_)
    have hc : IsCoprime (p : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
    obtain ⟨s, t, hst⟩ := hc
    have h1 : (s : C) * p + t * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) hst
    have := IsUltrametricDist.norm_add_le_max ((s : C) * p) (t * m)
    rw [h1, norm_one, norm_mul, norm_mul] at this
    refine absurd this (not_le.2 (max_lt ?_ ?_))
    · exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one C s)
        (norm_nonneg _) hlt
    · exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one C t)
        (norm_nonneg _) hm1
  have hnat : ∀ n : ℕ, ‖(n : C)‖ = ‖(n : ℚ_[p])‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
    have hm' : ‖(m : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm
    simp only [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, h, hcop m hm, hm', Padic.norm_p]
  have hint : ∀ n : ℤ, ‖(n : C)‖ = ‖(n : ℚ_[p])‖ := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [hnat]
  rw [Rat.cast_def, Rat.cast_def, norm_div, norm_div, hnat, hint]
end GlobalTheory
