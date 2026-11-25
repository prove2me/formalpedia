-- Prove2me | solution 1 for NeuralCollapseUFM.ce_loss_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:48:53.887735+00:00
-- url     : https://prove2.me/submissions/440ba217-f586-41f7-89ca-fc8034dee8e7

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Finset

namespace NeuralCollapseUFM

theorem ce_loss_lower_bound {K : ℕ} (hK : 2 ≤ K) (z : Fin K → ℝ) (k : Fin K) (c1 : ℝ)
    (hc1 : 0 < c1) :
    1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ≤ ceLoss z k ∧
    (ceLoss z k = 1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ↔
      (∀ i j, i ≠ k → j ≠ k → z i = z j) ∧
        c1 = (((K : ℝ) - 1) * Real.exp (((∑ i, z i) - K * z k) / ((K : ℝ) - 1)))⁻¹) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  set t := univ.erase k with ht
  have hct : (t.card : ℝ) = (K : ℝ) - 1 := by
    rw [ht, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ K)]; simp
  set w : ℝ := 1 / ((K : ℝ) - 1) with hw
  set T : ℝ := ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) with hT
  set d : Fin K → ℝ := fun i => z i - z k with hd
  have hw1 : ∑ i ∈ t, w = 1 := by
    rw [sum_const, nsmul_eq_mul, hct, hw]; field_simp
  have hwd : ∑ i ∈ t, w • d i = T := by
    simp only [smul_eq_mul, ← mul_sum, hd, sum_sub_distrib, sum_const, nsmul_eq_mul, hct]
    rw [ht, sum_erase_eq_sub (mem_univ k), hw, hT]
    field_simp; ring
  set A : ℝ := ∑ i ∈ t, w • Real.exp (d i) with hAdef
  have hjen := strictConvexOn_exp.convexOn.map_sum_le (t := t) (w := fun _ => w) (p := d)
    (fun _ _ => by rw [hw]; positivity) hw1 (fun _ _ => Set.mem_univ _)
  rw [hwd] at hjen
  have hjeq := strictConvexOn_exp.map_sum_eq_iff_of_pos (t := t) (w := fun _ => w) (p := d)
    (fun _ _ => by rw [hw]; positivity) hw1 (fun _ _ => Set.mem_univ _)
  rw [hwd] at hjeq
  -- A ≥ exp T ; loss = log (1 + (K-1) A)
  have hA : 1 + ((K : ℝ) - 1) * A = (∑ i, Real.exp (z i)) / Real.exp (z k) := by
    have : ((K : ℝ) - 1) * A = ∑ i ∈ t, Real.exp (z i) / Real.exp (z k) := by
      rw [hAdef, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, hd, Real.exp_sub, hw]; field_simp
    rw [this, ← sum_div, ht, sum_erase_eq_sub (mem_univ k)]
    field_simp; ring
  have hL : ceLoss z k = Real.log (1 + ((K : ℝ) - 1) * A) := by
    rw [hA, ceLoss, ← Real.log_inv, inv_div]
  have hET : 0 < Real.exp T := Real.exp_pos T
  -- concavity step
  set p : ℝ := 1 / (1 + c1) with hp
  set q : ℝ := c1 / (1 + c1) with hq
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  have hpq : q + p = 1 := by rw [hp, hq]; field_simp; ring
  set a : ℝ := (1 + c1) / c1 with ha
  set b : ℝ := (1 + c1) * ((K : ℝ) - 1) * Real.exp T with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : q • a + p • b = 1 + ((K : ℝ) - 1) * Real.exp T := by
    rw [smul_eq_mul, smul_eq_mul, hq, ha, hp, hb]; field_simp
  have hlogs : q • Real.log a + p • Real.log b = p * T + cTwo K c1 := by
    rw [smul_eq_mul, smul_eq_mul, hb, Real.log_mul (by positivity) hET.ne', Real.log_exp, cTwo,
      hp, hq, ha]
    ring
  have hconc : q • Real.log a + p • Real.log b ≤ Real.log (q • a + p • b) :=
    strictConcaveOn_log_Ioi.concaveOn.2 ha0 hb0 hq0.le hp0.le hpq
  have hstrict : a ≠ b → q • Real.log a + p • Real.log b < Real.log (q • a + p • b) :=
    fun hne => strictConcaveOn_log_Ioi.2 ha0 hb0 hne hq0 hp0 hpq
  rw [hab, hlogs] at hconc
  have hgoal : 1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) = p * T := by
    rw [hp, hT]; ring
  rw [hgoal, hL]
  have hmono : Real.log (1 + ((K : ℝ) - 1) * Real.exp T) ≤ Real.log (1 + ((K : ℝ) - 1) * A) :=
    Real.log_le_log (by positivity) (by nlinarith)
  refine ⟨hconc.trans hmono, ⟨fun heq => ?_, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have e1 : Real.log (1 + ((K : ℝ) - 1) * Real.exp T) = p * T + cTwo K c1 := by linarith
    have e2 : Real.log (1 + ((K : ℝ) - 1) * Real.exp T) = Real.log (1 + ((K : ℝ) - 1) * A) := by
      linarith
    have hApos : 0 < 1 + ((K : ℝ) - 1) * Real.exp T := by positivity
    have e3 : 1 + ((K : ℝ) - 1) * Real.exp T = 1 + ((K : ℝ) - 1) * A :=
      Real.log_injOn_pos hApos (by
        show 0 < 1 + ((K : ℝ) - 1) * A
        nlinarith) e2
    have e4 : Real.exp T = A := by
      have := mul_left_cancel₀ hK1.ne' (by linarith : ((K : ℝ) - 1) * Real.exp T = ((K : ℝ) - 1) * A)
      exact this
    have hjall := hjeq.1 (by simpa [hAdef] using e4)
    have hab' : a = b := by
      by_contra hne
      have := hstrict hne
      rw [hab, hlogs] at this
      linarith
    refine ⟨fun i j hi hj => ?_, ?_⟩
    · have := hjall (mem_erase.2 ⟨hi, mem_univ i⟩) (mem_erase.2 ⟨hj, mem_univ j⟩)
      simpa [hd] using this
    · rw [ha, hb] at hab'
      field_simp at hab' ⊢
      nlinarith [hab']
  · have hall : ∀ i ∈ t, ∀ j ∈ t, d i = d j := by
      intro i hi j hj
      simp only [hd]
      rw [hz i j (ne_of_mem_erase hi) (ne_of_mem_erase hj)]
    have e4 : Real.exp T = A := by simpa [hAdef] using hjeq.2 (fun i hi j hj => hall i hi j hj)
    have hab' : a = b := by
      rw [ha, hb, hc]
      have : ((K : ℝ) - 1) * Real.exp T ≠ 0 := by positivity
      field_simp
    rw [← e4, ← hab, ← hlogs, hab', ← add_smul, ← add_smul, hpq, one_smul, one_smul]

end NeuralCollapseUFM
open NeuralCollapseUFM in
theorem solution {K : ℕ} (hK : 2 ≤ K) (z : Fin K → ℝ) (k : Fin K) (c1 : ℝ)
    (hc1 : 0 < c1) :
    1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ≤ ceLoss z k ∧
    (ceLoss z k = 1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ↔
      (∀ i j, i ≠ k → j ≠ k → z i = z j) ∧
        c1 = (((K : ℝ) - 1) * Real.exp (((∑ i, z i) - K * z k) / ((K : ℝ) - 1)))⁻¹) :=
  ce_loss_lower_bound hK z k c1 hc1
