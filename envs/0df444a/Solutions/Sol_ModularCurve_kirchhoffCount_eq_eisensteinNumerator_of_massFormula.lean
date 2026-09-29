-- Prove2me | solution 1 for ModularCurve.kirchhoffCount_eq_eisensteinNumerator_of_massFormula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/21474b87-0d47-51ac-ae28-6b743f60c4e5

import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kirchhoffCount_eq_eisensteinNumerator_of_massFormula

open ModularCurve Finset

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (p : ℕ)
    (he : ∀ x, e x = 1 ∨ e x = 2 ∨ e x = 3)
    (h2 : ({x | e x = 2} : Set ι).Subsingleton)
    (h3 : ({x | e x = 3} : Set ι).Subsingleton)
    (hmass : ∑ x, ((e x : ℚ))⁻¹ = ((p : ℚ) - 1) / 12) :
    kirchhoffCount e = eisensteinNumerator p := by

  set a := (univ.filter fun x => e x = 2).card with ha_def
  set b := (univ.filter fun x => e x = 3).card with hb_def
  set n := (univ.filter fun x => e x = 1).card with hn_def
  have ha : a ≤ 1 := Finset.card_le_one.mpr fun x hx y hy =>
    h2 (by simpa using hx) (by simpa using hy)
  have hb : b ≤ 1 := Finset.card_le_one.mpr fun x hx y hy =>
    h3 (by simpa using hx) (by simpa using hy)
  have he0 : ∀ x, e x ≠ 0 := fun x => by rcases he x with h | h | h <;> omega

  have hind : ∀ x, e x = 2 ^ (if e x = 2 then 1 else 0) * 3 ^ (if e x = 3 then 1 else 0) := fun x => by
    rcases he x with h | h | h <;> simp [h]
  have hP : ∏ y, e y = 2 ^ a * 3 ^ b := by
    calc ∏ y, e y = ∏ y, (2 ^ (if e y = 2 then 1 else 0) * 3 ^ (if e y = 3 then 1 else 0)) :=
          Finset.prod_congr rfl fun y _ => hind y
      _ = 2 ^ a * 3 ^ b := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
            ← Finset.card_filter, ← Finset.card_filter]

  have hinv : ∀ x, ((e x : ℚ))⁻¹ =
      (if e x = 1 then 1 else 0) + (if e x = 2 then 1 else 0) / 2 + (if e x = 3 then 1 else 0) / 3 :=
    fun x => by rcases he x with h | h | h <;> simp [h]
  have hsum : ∑ x, ((e x : ℚ))⁻¹ = n + a / 2 + b / 3 := by
    rw [Finset.sum_congr rfl fun x _ => hinv x, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]

  have hpQ : (p : ℚ) = 12 * n + 6 * a + 4 * b + 1 := by
    rw [hsum] at hmass
    linarith
  have hp : p = 12 * n + 6 * a + 4 * b + 1 := by exact_mod_cast hpQ

  have hK : (kirchhoffCount e : ℚ) = ((2 ^ a * 3 ^ b : ℕ) : ℚ) * (n + a / 2 + b / 3) := by
    rw [← hsum, Finset.mul_sum, kirchhoffCount_def, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hP, ← Finset.prod_erase_mul _ _ (Finset.mem_univ x), Nat.cast_mul,
      mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr (he0 x))]

  subst hp
  interval_cases a <;> interval_cases b
  · have hKn : (kirchhoffCount e : ℚ) = ((n : ℕ) : ℚ) := by rw [hK]; push_cast; ring
    rw [Nat.cast_injective hKn, eisensteinNumerator]
    have hg : Nat.gcd (12 * n + 6 * 0 + 4 * 0 + 1 - 1) 12 = 12 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, show (12 * n + 6 * 0 + 4 * 0 + 1 - 1) % 12 = 0 by omega]; rfl
    rw [hg]; omega
  · have hKn : (kirchhoffCount e : ℚ) = ((3 * n + 1 : ℕ) : ℚ) := by rw [hK]; push_cast; ring
    rw [Nat.cast_injective hKn, eisensteinNumerator]
    have hg : Nat.gcd (12 * n + 6 * 0 + 4 * 1 + 1 - 1) 12 = 4 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, show (12 * n + 6 * 0 + 4 * 1 + 1 - 1) % 12 = 4 by omega]; rfl
    rw [hg]; omega
  · have hKn : (kirchhoffCount e : ℚ) = ((2 * n + 1 : ℕ) : ℚ) := by rw [hK]; push_cast; ring
    rw [Nat.cast_injective hKn, eisensteinNumerator]
    have hg : Nat.gcd (12 * n + 6 * 1 + 4 * 0 + 1 - 1) 12 = 6 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, show (12 * n + 6 * 1 + 4 * 0 + 1 - 1) % 12 = 6 by omega]; rfl
    rw [hg]; omega
  · have hKn : (kirchhoffCount e : ℚ) = ((6 * n + 5 : ℕ) : ℚ) := by rw [hK]; push_cast; ring
    rw [Nat.cast_injective hKn, eisensteinNumerator]
    have hg : Nat.gcd (12 * n + 6 * 1 + 4 * 1 + 1 - 1) 12 = 2 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, show (12 * n + 6 * 1 + 4 * 1 + 1 - 1) % 12 = 10 by omega]; rfl
    rw [hg]; omega

end S_ModularCurve_kirchhoffCount_eq_eisensteinNumerator_of_massFormula
end P2MW
export P2MW.S_ModularCurve_kirchhoffCount_eq_eisensteinNumerator_of_massFormula (solution)
