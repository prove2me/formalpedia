-- Prove2me | solution 1 for LonelyRunnerConjecture.classical_small_cases
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T21:08:36.451562+00:00
-- url     : https://prove2.me/submissions/a8b61067-9a36-4ed9-b1cf-7f07628f1ce1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs
import Theorems.Thm_LonelyRunnerConjecture_four_runners
import Theorems.Thm_LonelyRunnerConjecture_five_runners
import Theorems.Thm_LonelyRunnerConjecture_six_runners
import Theorems.Thm_LonelyRunnerConjecture_seven_runners

namespace LonelyRunnerConjecture.SmallCasesAux
open LonelyRunnerConjecture

lemma dist_add_int (x : ℝ) (n : ℤ) : distToNearestInt (x + n) = distToNearestInt x := by
  simp [distToNearestInt, Int.fract_add_intCast]

lemma dist_neg (x : ℝ) : distToNearestInt (-x) = distToNearestInt x := by
  unfold distToNearestInt
  by_cases h : Int.fract x = 0
  · have h' : Int.fract (-x) = 0 := by rw [Int.fract_neg_eq_zero]; exact h
    rw [h, h']
  · rw [Int.fract_neg h, sub_sub_cancel, min_comm]

lemma dist_of_mem (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) :
    distToNearestInt x = min x (1 - x) := by
  unfold distToNearestInt
  rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]

theorem lrc_zero : LRC 0 := by
  intro S hS _
  refine ⟨0, ?_⟩
  intro v hv
  rw [Finset.card_eq_zero] at hS
  simp [hS] at hv

theorem lrc_one : LRC 1 := by
  intro S hS hpos
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
  have ha : (0 : ℝ) < a := by exact_mod_cast hpos a (Finset.mem_singleton_self a)
  refine ⟨1 / (2 * a), ?_⟩
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  have : 1 / (2 * (v : ℝ)) * v = 1 / 2 := by field_simp
  rw [this, dist_of_mem _ (by norm_num) (by norm_num)]
  norm_num

theorem lrc_two : LRC 2 := by
  intro S hS hpos
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  set g := Nat.gcd a b with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime a' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hgpos
    rwa [← hg, ha', hb', Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos] at this
  have ha'pos : 0 < a' := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · rw [h] at ha'; omega
    · exact h
  have hb'pos : 0 < b' := by
    rcases Nat.eq_zero_or_pos b' with h | h
    · rw [h] at hb'; omega
    · exact h
  have hab' : a' ≠ b' := by
    intro h; apply hab; rw [ha', hb', h]
  set M := a' + b' with hM
  have hM3 : 3 ≤ M := by omega
  have hcopM : Nat.Coprime a' M := by
    rw [hM]
    exact (Nat.coprime_add_self_right).mpr hcop |>.symm.symm |> fun h => by
      simpa [Nat.Coprime, Nat.gcd_comm, add_comm] using
        (Nat.coprime_add_self_right (m := a') (n := b')).mpr hcop
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopM (by omega)
  set m := (M + 2) / 3 with hm
  have hm1 : M ≤ 3 * m := by omega
  have hm2 : 3 * m ≤ 2 * M := by omega
  have hmM : m < M := by omega
  set u := w * m with hu
  have hmod : a' * u % M = m := by
    rw [hu, ← mul_assoc, Nat.mul_mod, hw, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hmM]
  set q := a' * u / M with hq
  have hdiv : a' * u = M * q + m := by rw [← hmod, hq]; exact (Nat.div_add_mod _ _).symm
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  set X : ℝ := (m : ℝ) / M with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1 : X < 1 := by rw [hX, div_lt_one hMpos]; exact_mod_cast hmM
  have hXlo : 1 / 3 ≤ X := by
    rw [hX, le_div_iff₀ hMpos]; have : (M : ℝ) ≤ 3 * m := by exact_mod_cast hm1
    linarith
  have hXhi : X ≤ 2 / 3 := by
    rw [hX, div_le_iff₀ hMpos]; have : (3 * m : ℝ) ≤ 2 * M := by exact_mod_cast hm2
    linarith
  have hdX : 1 / 3 ≤ distToNearestInt X := by
    rw [dist_of_mem X hX0 hX1]
    exact le_min hXlo (by linarith)
  have hdivR : (a' : ℝ) * u = M * q + m := by exact_mod_cast hdiv
  have hMR : (M : ℝ) = a' + b' := by rw [hM]; push_cast; ring
  refine ⟨(u : ℝ) / (g * M), ?_⟩
  intro v hv
  have hk : (1 : ℝ) / ((2 : ℕ) + 1 : ℝ) = 1 / 3 := by norm_num
  rw [hk]
  rcases Finset.mem_insert.mp hv with rfl | hv
  · have : (u : ℝ) / (g * M) * (v : ℝ) = X + (q : ℤ) := by
      rw [ha']; push_cast
      rw [hX]; field_simp
      linear_combination hdivR
    rw [this, dist_add_int]; exact hdX
  · rw [Finset.mem_singleton] at hv
    subst hv
    have : (u : ℝ) / (g * M) * (v : ℝ) = -X + ((u : ℤ) - (q : ℤ) : ℤ) := by
      rw [hb']; push_cast
      rw [hX]; field_simp
      linear_combination (-1 : ℝ) * hdivR - (u : ℝ) * hMR
    rw [this, dist_add_int, dist_neg]; exact hdX

end LonelyRunnerConjecture.SmallCasesAux

open LonelyRunnerConjecture LonelyRunnerConjecture.SmallCasesAux in
theorem solution : ∀ k : ℕ, k ≤ 6 → LRC k := by
  intro k hk
  interval_cases k
  · exact lrc_zero
  · exact lrc_one
  · exact lrc_two
  · exact LonelyRunnerConjecture.four_runners
  · exact LonelyRunnerConjecture.five_runners
  · exact LonelyRunnerConjecture.six_runners
  · exact LonelyRunnerConjecture.seven_runners
