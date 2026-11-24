-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.idealCount_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:40.347649+00:00
-- url     : https://prove2.me/submissions/b9df4f69-8a48-4b98-8e1c-5c05fc189dbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_idealCount_prime_mul
import Theorems.Thm_GlobalTheory_QuadraticZeta_sum_divisors_prime_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (h2 : finrank ℚ K = 2) {R : Type*} [CommRing R] (χ : ℕ → R)
    (h1 : χ 1 = 1) (hχ : ∀ a b, χ (a * b) = χ a * χ b)
    (hκ : ∀ p : ℕ, p.Prime → χ p = kroneckerAt (discr K) p) {m : ℕ} (hm : m ≠ 0) :
    (idealCount K m : R) = ∑ e ∈ m.divisors, χ e := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [idealCount, Ideal.absNorm_eq_one_iff, h1]
    obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd hm1
    have hk : k ≠ 0 := right_ne_zero_of_mul hm
    have hlt : k < p * k := lt_mul_left (Nat.pos_of_ne_zero hk) hp.one_lt
    have := congrArg (Int.cast : ℤ → R) (idealCount_prime_mul h2 hp k)
    push_cast at this
    rw [this, sum_divisors_prime_mul χ hχ hp hk, hκ p hp, ih k hlt hk]
    congr 2
    split_ifs with h
    · exact ih _ ((Nat.div_le_self _ _).trans_lt hlt)
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h) hp.pos).ne'
    · rfl
end GlobalTheory.QuadraticZeta
