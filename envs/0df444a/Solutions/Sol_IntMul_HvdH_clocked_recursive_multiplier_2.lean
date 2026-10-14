-- Prove2me | solution 2 for IntMul.HvdH.clocked_recursive_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-13T21:39:51.752081+00:00
-- url     : https://prove2.me/submissions/ef622139-3f4d-4dc9-8704-78a93a923d6c

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_HvdH_StepParameters
import Theorems.Thm_IntMul_HvdH_theorem_1_1

set_option maxHeartbeats 1000000

namespace HvdHCorM

open IntMul

theorem mulAt_mono {M : MultitapeTM} {n : ℕ} {T T' : ℝ} (h : MultipliesAt M n T) (hT : T ≤ T') :
    MultipliesAt M n T' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hT, hh⟩

theorem mulAt_nonneg {M : MultitapeTM} {n : ℕ} {T : ℝ} (h : MultipliesAt M n T) : 0 ≤ T := by
  obtain ⟨t, ht, -⟩ := h (List.replicate n false) (List.replicate n false) (by simp) (by simp)
  exact le_trans (Nat.cast_nonneg t) ht

theorem nlog_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * Real.log n :=
  mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n)

theorem nlog_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℝ) * Real.log n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (by linarith) (Real.log_pos h1)

theorem all_ge_two (M : MultitapeTM) (hM : ∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) :
    ∀ n0 : ℕ, ∀ c : ℝ, (∀ n : ℕ, n0 ≤ n → 2 ≤ n → MultipliesAt M n (c * ((n : ℝ) * Real.log n))) →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → MultipliesAt M n (C * ((n : ℝ) * Real.log n)) := by
  intro n0
  induction n0 with
  | zero =>
    intro c hc
    exact ⟨max c 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun n hn =>
      mulAt_mono (hc n (Nat.zero_le _) hn) (mul_le_mul_of_nonneg_right (le_max_left _ _) (nlog_nonneg n))⟩
  | succ k ih =>
    intro c hc
    by_cases hk : 2 ≤ k
    · obtain ⟨τ, hτ⟩ := hM k (by omega)
      have hpos := nlog_pos hk
      apply ih (max c (τ / ((k : ℝ) * Real.log k)))
      intro n hn h2
      rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · refine mulAt_mono hτ ?_
        have : τ / ((k : ℝ) * Real.log k) * ((k : ℝ) * Real.log k) = τ := div_mul_cancel₀ _ hpos.ne'
        calc τ = τ / ((k : ℝ) * Real.log k) * ((k : ℝ) * Real.log k) := this.symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
      · exact mulAt_mono (hc n hlt h2) (mul_le_mul_of_nonneg_right (le_max_left _ _) (nlog_nonneg n))
    · exact ih c (fun n hn h2 => hc n (by omega) h2)

theorem uniform (h : MulTimeBound fun n => (n : ℝ) * Real.log n) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → MultipliesAt M n (C * ((n : ℝ) * Real.log n)) := by
  obtain ⟨M, hM, c, -, n0, hc⟩ := h
  exact ⟨M, hM, all_ge_two M hM n0 c (fun n hn h2 => hc n hn (by omega))⟩

theorem sInf_le' {M : MultitapeTM} {n : ℕ} {T : ℝ} (h : MultipliesAt M n T) :
    sInf {τ : ℝ | MultipliesAt M n τ} ≤ T :=
  csInf_le ⟨0, fun _ hx => mulAt_nonneg hx⟩ h

theorem sInf_nonneg' (M : MultitapeTM) (n : ℕ) : 0 ≤ sInf {τ : ℝ | MultipliesAt M n τ} :=
  Real.sInf_nonneg (fun _ hx => mulAt_nonneg hx)

theorem two_le_of_pow {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) : 2 ≤ n := by
  have h1 : 1 ≤ d ^ 12 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ 1 ≤ 2 ^ (d ^ 12) := Nat.pow_le_pow_right (by norm_num) h1
  omega

end HvdHCorM

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : IntMul.MultitapeTM,
      (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, IntMul.MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n b p T r : ℕ, IntMul.HvdH.StepParameters d n b p T r →
        ∀ τ : ℝ, IntMul.MultipliesAt M (3 * r * p) τ →
          IntMul.MultipliesAt M n
            (12 * (T : ℝ) / r * τ + C * ((n : ℝ) * Real.log n)) := by
  obtain ⟨M, hM, C, -, hC⟩ := HvdHCorM.uniform IntMul.HvdH.theorem_1_1
  refine ⟨M, hM, C, fun n b p T r hP τ hτ => HvdHCorM.mulAt_mono (hC n (HvdHCorM.two_le_of_pow hd hP.1)) ?_⟩
  have h0 := HvdHCorM.mulAt_nonneg hτ
  have h1 : 0 ≤ 12 * (T : ℝ) / r := by positivity
  nlinarith [mul_nonneg h1 h0]
