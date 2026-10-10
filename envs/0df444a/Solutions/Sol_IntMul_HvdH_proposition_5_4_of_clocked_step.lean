-- Prove2me | solution 1 for IntMul.HvdH.proposition_5_4_of_clocked_step
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T14:36:33.303685+00:00
-- url     : https://prove2.me/submissions/fc25edaa-2158-45e0-afc5-9e17eeaa6163

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_HvdH_StepParameters
import Theorems.Thm_IntMul_multipliesAt_sInf
import Theorems.Thm_IntMul_HvdH_recursive_size_decreases
import Mathlib.Tactic

open IntMul IntMul.HvdH

private lemma budgets_bddBelow (M : MultitapeTM) (n : ℕ) :
    BddBelow {τ : ℝ | MultipliesAt M n τ} := by
  refine ⟨0, fun τ hτ => ?_⟩
  obtain ⟨t, ht, _⟩ := hτ (List.replicate n false) (List.replicate n false)
    (by simp) (by simp)
  exact (Nat.cast_nonneg t).trans ht

/-- A verified clocked machine step implies the exact strict recurrence of Proposition 5.4.
The hypothesis `hclock` is the outstanding implementation and complexity obligation. -/
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (M : MultitapeTM) (hcorrect : ∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ)
    (C : ℝ)
    (hclock : ∀ n b p T r : ℕ, StepParameters d n b p T r →
      ∀ τ : ℝ, MultipliesAt M (3 * r * p) τ →
        MultipliesAt M n (12 * (T : ℝ) / r * τ + C * ((n : ℝ) * Real.log n))) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n : ℕ, 2 ^ (d ^ 12) ≤ n →
        ∀ b p T r : ℕ, b = Nat.clog 2 n → p = 6 * b →
          (∃ k : ℕ, T = 2 ^ k) → 4 * (n : ℝ) / b ≤ T → (T : ℝ) < 8 * (n : ℝ) / b →
          (∃ j : ℕ, r = 2 ^ j) → (T : ℝ) ^ ((1 : ℝ) / d) ≤ r →
          (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) →
          sInf {τ : ℝ | MultipliesAt M n τ} <
            12 * (T : ℝ) / r * sInf {τ : ℝ | MultipliesAt M (3 * r * p) τ} +
              C * ((n : ℝ) * Real.log n) := by
  refine ⟨M, hcorrect, C + 1, ?_⟩
  intro n hn b p T r hb hp hTpow hT1 hT2 hrpow hr1 hr2
  have hparams : StepParameters d n b p T r :=
    ⟨hn, hb, hp, hTpow, hT1, hT2, hrpow, hr1, hr2⟩
  have hm := (recursive_size_decreases d n b p T r hd hparams).1
  have hsmall := IntMul.multipliesAt_sInf (hcorrect (3 * r * p) hm)
  have hbudget := hclock n b p T r hparams _ hsmall
  have hupper := csInf_le (budgets_bddBelow M n) hbudget
  have hd0 : 0 < d := by omega
  have hn2 : 2 ≤ n :=
    le_trans (Nat.succ_le_of_lt
      (Nat.one_lt_two_pow (by positivity) : 1 < 2 ^ (d ^ 12))) hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hpositive : 0 < (n : ℝ) * Real.log n := mul_pos (by linarith) hlog
  exact hupper.trans_lt (by nlinarith)


