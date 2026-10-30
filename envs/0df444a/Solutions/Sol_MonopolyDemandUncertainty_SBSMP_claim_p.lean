-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.claim_p
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:52:55.873076+00:00
-- url     : https://prove2.me/submissions/1b90f5ae-4018-4946-8a2f-d57d538700e5

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

open MeasureTheory Set

namespace Aux_MDU_CP
open MonopolyDemandUncertainty.SBSMP

lemma prob_pos (E : Economy) (hE : E.Valid) (i : Fin 2) : 0 < E.prob i := by
  fin_cases i
  · simp [Economy.prob]; linarith [hE.α₁_pos]
  · simp [Economy.prob]; linarith [hE.α₁_lt_one]

lemma dens_pos (E : Economy) (h1 : E.Condition1) (i : Fin 2) (v : ℝ) (hv : v ∈ E.V) :
    0 < E.dens i v := by
  unfold Economy.dens; linarith [h1.2 i v hv]

lemma dens_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (E.dens i) := by
  unfold Economy.dens
  exact ((h1.1 i).continuous_deriv (by norm_num)).neg

lemma Z_strictAnti (E : Economy) (h2 : E.Condition2) : StrictAntiOn E.Z E.V := by
  have hd : ∀ v ∈ E.V, DifferentiableAt ℝ E.Z v := fun v hv =>
    differentiableAt_of_deriv_ne_zero (ne_of_lt (h2 v hv))
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun v hv => (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    exact h2 v (interior_subset hv)

lemma int_le_of_pointwise {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hg : IntegrableOn g s) (hf0 : ∀ x ∈ s, 0 ≤ f x) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ≤ ∫ x in s, g x :=
  integral_mono_of_nonneg ((ae_restrict_iff' hs).mpr (ae_of_all _ hf0)) hg
    ((ae_restrict_iff' hs).mpr (ae_of_all _ h))

lemma sbsmp_EIR (E : Economy) (hE : E.Valid) (a b : ℝ) (ha : a ∈ E.V) (hb : b ∈ E.V) :
    E.IsEIR (sbsmp a b) := by
  intro i v hv
  have hv0 : 0 ≤ v := le_trans hE.vlo_nonneg hv.1
  have ha0 : 0 ≤ a := le_trans hE.vlo_nonneg ha.1
  have hb0 : 0 ≤ b := le_trans hE.vlo_nonneg hb.1
  fin_cases i
  · simp only [sbsmp, Fin.zero_eta, Matrix.cons_val_zero]
    split_ifs with h <;> constructor <;> linarith
  · simp only [sbsmp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    split_ifs with h <;> constructor <;> linarith

lemma term_le (c v vhat w : ℝ) (hw : 0 ≤ w) :
    (v - (if c ≤ vhat then c else 0)) * ind (decide (c ≤ vhat)) * w ≤
      (v - (if c ≤ v then c else 0)) * ind (decide (c ≤ v)) * w := by
  by_cases h1 : c ≤ vhat <;> by_cases h2 : c ≤ v <;> simp [ind, h1, h2]
  · nlinarith
  · nlinarith

lemma sbsmp_BIC (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (a b : ℝ) :
    E.IsBIC (sbsmp a b) := by
  intro v hv vhat _
  have hw0 : 0 ≤ E.prob 0 * E.dens 0 v :=
    (mul_pos (prob_pos E hE 0) (dens_pos E h1 0 v hv)).le
  have hw1 : 0 ≤ E.prob 1 * E.dens 1 v :=
    (mul_pos (prob_pos E hE 1) (dens_pos E h1 1 v hv)).le
  unfold Economy.payoff
  simp only [Fin.sum_univ_two, sbsmp, Matrix.cons_val_zero, Matrix.cons_val_one]
  have t0 := term_le a v vhat _ hw0
  have t1 := term_le b v vhat _ hw1
  simp only [mul_assoc] at t0 t1 ⊢
  linarith

end Aux_MDU_CP

open MonopolyDemandUncertainty.SBSMP Aux_MDU_CP in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) (a b : ℝ) (ha : E.vlo ≤ a) (hab : a < b) (hb : b ≤ E.vhi)
    (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M)
    (hx0 : ∀ v ∈ E.V, M.x 0 v = decide (a ≤ v)) (hx1 : ∀ v ∈ E.V, M.x 1 v = decide (b ≤ v))
    (hta : M.t 0 a = a) :
    (∫ v in Icc b E.vhi, ∑ i, M.t i v * E.prob i * E.dens i v ≤
        ∫ v in Icc b E.vhi, (a * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v)) ∧
      E.IsBIC (sbsmp a b) ∧ E.IsEIR (sbsmp a b) := by
  have haV : a ∈ E.V := ⟨ha, by linarith⟩
  have hbV : b ∈ E.V := ⟨by linarith, hb⟩
  refine ⟨?_, sbsmp_BIC E hE h1 a b, sbsmp_EIR E hE a b haV hbV⟩
  have hsub : ∀ v ∈ Icc b E.vhi, v ∈ E.V := fun v hv => ⟨by linarith [hv.1], hv.2⟩
  -- allocations
  have xa0 : M.x 0 a = true := by rw [hx0 a haV]; simp
  have xa1 : M.x 1 a = false := by rw [hx1 a haV]; simp; linarith
  have xb0 : M.x 0 b = true := by rw [hx0 b hbV]; simp; linarith
  have xb1 : M.x 1 b = true := by rw [hx1 b hbV]; simp
  -- BIC of b w.r.t. a
  have kb : (M.t 0 b - a) * (E.prob 0 * E.dens 0 b) ≤
      (b - M.t 1 b) * (E.prob 1 * E.dens 1 b) := by
    have hh := hBIC b hbV a haV
    simp only [Economy.payoff, Fin.sum_univ_two, ind, xa0, xa1, xb0, xb1, hta] at hh
    simp only [if_true, Bool.false_eq_true, if_false] at hh
    nlinarith [hh]
  have ht1b := (hEIR 1 b hbV).2
  apply int_le_of_pointwise measurableSet_Icc
  · have hc : Continuous (fun v => a * E.prob 0 * E.dens 0 v + b * E.prob 1 * E.dens 1 v) :=
      ((continuous_const.mul (dens_cont E h1 0)).add (continuous_const.mul (dens_cont E h1 1)))
    exact hc.integrableOn_Icc
  · intro v hv
    have hvV := hsub v hv
    rw [Fin.sum_univ_two]
    have := (hEIR 0 v hvV).1
    have := (hEIR 1 v hvV).1
    have := mul_pos (prob_pos E hE 0) (dens_pos E h1 0 v hvV)
    have := mul_pos (prob_pos E hE 1) (dens_pos E h1 1 v hvV)
    nlinarith
  · intro v hv
    have hvV := hsub v hv
    have xv0 : M.x 0 v = true := by rw [hx0 v hvV]; simp; linarith [hv.1]
    have xv1 : M.x 1 v = true := by rw [hx1 v hvV]; simp; exact hv.1
    -- BIC of v w.r.t. b
    have kv : M.t 0 v * (E.prob 0 * E.dens 0 v) + M.t 1 v * (E.prob 1 * E.dens 1 v) ≤
        M.t 0 b * (E.prob 0 * E.dens 0 v) + M.t 1 b * (E.prob 1 * E.dens 1 v) := by
      have hh := hBIC v hvV b hbV
      simp only [Economy.payoff, Fin.sum_univ_two, ind, xb0, xb1, xv0, xv1] at hh
      simp only [if_true, Bool.false_eq_true, if_false] at hh
      nlinarith [hh]
    -- likelihood ratio monotone: w1(v) w2(b) ≤ w1(b) w2(v)
    set A := E.prob 0 * E.dens 0 b
    set B := E.prob 1 * E.dens 1 b
    set C := E.prob 0 * E.dens 0 v
    set Dd := E.prob 1 * E.dens 1 v
    have hA : 0 < A := mul_pos (prob_pos E hE 0) (dens_pos E h1 0 b hbV)
    have hC : 0 < C := mul_pos (prob_pos E hE 0) (dens_pos E h1 0 v hvV)
    have hZ : C * B ≤ A * Dd := by
      rcases eq_or_lt_of_le hv.1 with h | h
      · simp only [A, B, C, Dd]; rw [← h]
      · have hz := Z_strictAnti E h2 hbV hvV h
        unfold Economy.Z at hz
        rw [div_lt_div_iff₀ (dens_pos E h1 1 v hvV) (dens_pos E h1 1 b hbV)] at hz
        have := mul_lt_mul_of_pos_left hz (mul_pos (prob_pos E hE 0) (prob_pos E hE 1))
        simp only [A, B, C, Dd]; nlinarith
    have s1 : (M.t 0 b - a) * A * C ≤ (b - M.t 1 b) * B * C :=
      mul_le_mul_of_nonneg_right kb hC.le
    have s2 : (b - M.t 1 b) * (C * B) ≤ (b - M.t 1 b) * (A * Dd) :=
      mul_le_mul_of_nonneg_left hZ (by linarith)
    have s3 : (M.t 0 b - a) * C ≤ (b - M.t 1 b) * Dd := by
      have : ((M.t 0 b - a) * C) * A ≤ ((b - M.t 1 b) * Dd) * A := by nlinarith
      exact le_of_mul_le_mul_right this hA
    rw [Fin.sum_univ_two]
    simp only [mul_assoc] at kv s3 ⊢
    nlinarith
