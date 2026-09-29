-- Prove2me | solution 1 for NetworkControl.GeneralCosts.theorem_ecca_performance
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:58:55.525235+00:00
-- url     : https://prove2.me/submissions/f2293ba6-bf5d-46bb-a661-45d755ec8c03

import Mathlib
import Definitions.Def_NetworkControl_GeneralCosts_eccaAdmitted
import Definitions.Def_NetworkControl_GeneralCosts_virtualPowerQueue

namespace NetworkControl.GeneralCosts

lemma aux_ecca_vpq_zero (Pav : ℝ) (hPav : 0 < Pav) (t : ℕ) :
    virtualPowerQueue (L := 1) (fun _ _ => (0 : ℝ)) Pav t = 0 := by
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [virtualPowerQueue, ih, Finset.sum_const_zero, add_zero, zero_sub]
    exact max_eq_right (by linarith)

end NetworkControl.GeneralCosts

open NetworkControl.GeneralCosts

theorem solution : ¬ (∀
    {L : ℕ} {Chan : Type}
    (V Rhat Pmax Pav β : ℝ) (hV : 0 ≤ V) (hRhat : 0 ≤ Rhat) (hPmax : 0 < Pmax)
    (hPav : 0 < Pav) (hPavLtPmax : Pav < Pmax) (hβ : 0 < β)
    (A : ℕ → Fin L → ℝ) (hA0 : ∀ t i, 0 ≤ A t i) (hAle : ∀ t i, A t i ≤ Rhat)
    (S : ℕ → Chan)
    (C : (Fin L → ℝ) → Chan → Fin L → ℝ)
    (hCbeta : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), (∑ j : Fin L, P j) ≤ Pmax →
      C P s i ≤ C (Function.update P i 0) s i + β * P i)
    (U : ℕ → Fin L → ℝ) (hU0 : ∀ i : Fin L, U 0 i = 0)
    (P : ℕ → Fin L → ℝ) (hPnonneg : ∀ t : ℕ, ∀ i : Fin L, 0 ≤ P t i)
    (hPbudget : ∀ t : ℕ, (∑ i : Fin L, P t i) ≤ Pmax)
    (D : ℕ → ℝ) (hDeq : ∀ t : ℕ, D t = virtualPowerQueue P Pav t)
    (hPopt : ∀ t : ℕ, ∀ P' : Fin L → ℝ, (∀ i : Fin L, 0 ≤ P' i) → (∑ i : Fin L, P' i) ≤ Pmax →
      (∑ i : Fin L, (U t i * C P' (S t) i - D t * P' i))
        ≤ ∑ i : Fin L, (U t i * C (P t) (S t) i - D t * (P t) i))
    (hUrec : ∀ t : ℕ, ∀ i : Fin L,
      U (t + 1) i = max (U t i - C (P t) (S t) i) 0 + eccaAdmitted (U t i) V (A t i)),
    (∀ t : ℕ, ∀ i : Fin L, U t i ≤ V + Rhat) ∧
      (∀ t : ℕ, D t ≤ β * V + β * Rhat + Pmax) ∧
      (∀ t0 T : ℕ, (∑ τ ∈ Finset.range T, ∑ i : Fin L, P (t0 + τ) i)
        ≤ Pav * (T : ℝ) + (β * V + β * Rhat + Pmax))) := by
  intro h
  have key := (@h 1 PUnit 0 0 2 1 1 le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ => PUnit.unit)
    (fun Q _ i => min (Q i) 0 - 1)
    (by
      intro Q s i _
      simp only [Function.update_self, min_self, one_mul]
      rcases le_total (Q i) 0 with hq | hq
      · rw [min_eq_left hq]; linarith
      · rw [min_eq_right hq]; linarith)
    (fun t _ => (t : ℝ)) (fun _ => by simp)
    (fun _ _ => 0) (fun _ _ => le_rfl)
    (fun _ => by simp)
    (fun _ => 0) (fun t => (aux_ecca_vpq_zero 1 one_pos t).symm)
    (by
      intro t Q hQ _
      apply Finset.sum_le_sum
      intro i _
      simp [min_eq_right (hQ i)])
    (by
      intro t i
      simp only [min_self, zero_sub, sub_neg_eq_add, eccaAdmitted, ite_self, add_zero]
      push_cast
      rw [max_eq_left (by positivity)])).1 1 0
  norm_num at key
