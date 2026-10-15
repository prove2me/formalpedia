-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.positive_rational_q_finite_family_has_integer_common_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T20:45:51.697378+00:00
-- url     : https://prove2.me/submissions/525f768c-3f7f-4919-9b5b-af929d5e6e33

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution
    {n : ℕ} (q : Fin n → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ S : ℚ, 0 < S ∧ ∃ e : Fin n → ℕ, (∀ i, 0 < e i) ∧
      ∀ i, S = (e i : ℚ) * q i := by
  let a : Fin n → ℕ := fun i => Int.toNat (q i).num
  have hnumInt (i : Fin n) : ((a i : ℕ) : ℤ) = (q i).num := by
    dsimp [a]
    exact Int.natCast_toNat_eq_self.mpr
      (le_of_lt (Rat.num_pos.mpr (hq i)))
  have hnum (i : Fin n) : (a i : ℚ) = (q i).num := by
    exact_mod_cast hnumInt i
  have ha (i : Fin n) : 0 < a i := by
    have h : (0 : ℚ) < (a i : ℚ) := by
      rw [hnum]
      exact_mod_cast (Rat.num_pos.mpr (hq i))
    exact_mod_cast h
  let P : ℕ := ∏ i : Fin n, a i
  have hP : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i hi => ha i
  have hdvd (i : Fin n) : a i ∣ P := by
    dsimp [P]
    exact Finset.dvd_prod_of_mem (fun j : Fin n => a j) (Finset.mem_univ i)
  let e : Fin n → ℕ := fun i => (P / a i) * (q i).den
  have hepos (i : Fin n) : 0 < e i := by
    dsimp [e]
    apply Nat.mul_pos
    · exact Nat.div_pos (Nat.le_of_dvd hP (hdvd i)) (ha i)
    · exact Rat.den_pos (q i)
  refine ⟨(P : ℚ), by exact_mod_cast hP, e, hepos, ?_⟩
  intro i
  symm
  rw [← Rat.num_div_den (q i)]
  simp only [e, Nat.cast_mul]
  have hden : ((q i).den : ℚ) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero (q i)
  field_simp [hden]
  rw [← hnum i]
  exact_mod_cast (Nat.div_mul_cancel (hdvd i))