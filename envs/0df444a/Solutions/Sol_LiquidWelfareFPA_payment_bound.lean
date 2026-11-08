-- Prove2me | solution 1 for LiquidWelfareFPA.payment_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:49:05.030411+00:00
-- url     : https://prove2.me/submissions/7ec84691-d134-4529-af18-775378d88f7a

import Mathlib
import Definitions.Def_LiquidWelfareFPA_IsTieRule
import Definitions.Def_LiquidWelfareFPA_CR

open LiquidWelfareFPA in
theorem solution {n T : ℕ} (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (hwin : IsTieRule o win) (γ Reg : ℝ) (hγ : 1 ≤ γ)
    (i : Fin n) (hCR : CR B o win γ Reg i) :
    0 ≤ o.pay i ∧ o.pay i ≤ min (B i) (o.val i) + max Reg 0 / γ := by
  have hrem : ∀ k, remBudget B o win i 0 k = B i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [remBudget, ih]
      split_ifs <;> simp [min_eq_left (hB i)]
  have hbhat : ∀ t, bhat B o win i 0 t = 0 := by
    intro t
    unfold bhat
    rw [hrem, zero_mul, min_eq_left (hB i)]
  have hU0 : 0 ≤ Uhat B o win i 0 := by
    unfold Uhat
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · rw [hbhat, sub_zero]; exact o.v_nonneg i t
    · exact le_refl 0
  have hbench : 0 ≤ bench B o win i := by
    unfold bench
    by_cases hbdd : BddAbove (Set.range fun lam : Set.Icc (0 : ℝ) 1 => Uhat B o win i lam)
    · exact le_trans hU0 (le_ciSup hbdd (⟨0, le_refl 0, zero_le_one⟩ : Set.Icc (0 : ℝ) 1))
    · rw [Real.iSup_of_not_bddAbove hbdd]
  have hpay : 0 ≤ o.pay i := by
    unfold Outcome.pay
    exact Finset.sum_nonneg (fun t _ => o.bid_nonneg _ _)
  refine ⟨hpay, ?_⟩
  obtain ⟨h1, h2⟩ := hCR
  have hγ0 : 0 < γ := by linarith
  have hm : 0 ≤ max Reg 0 / γ := div_nonneg (le_max_right _ _) hγ0.le
  have h3 : (Reg - bench B o win i) / γ ≤ max Reg 0 / γ :=
    div_le_div_of_nonneg_right (by linarith [le_max_left Reg 0]) hγ0.le
  have h4 : (bench B o win i - Reg) / γ = -((Reg - bench B o win i) / γ) := by ring
  rw [h4] at h2
  rcases le_total (B i) (o.val i) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith
