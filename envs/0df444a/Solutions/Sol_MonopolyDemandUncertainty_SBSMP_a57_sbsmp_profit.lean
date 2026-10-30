-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.a57_sbsmp_profit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:49:25.210694+00:00
-- url     : https://prove2.me/submissions/65a49d22-173e-44f1-95d9-856bb62ac8af

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

open MeasureTheory Set

namespace Aux_MDU_A57
open MonopolyDemandUncertainty.SBSMP

lemma dens_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (E.dens i) := by
  unfold Economy.dens
  exact ((h1.1 i).continuous_deriv (by norm_num)).neg

lemma D_diff (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Differentiable ℝ (E.D i) :=
  (h1.1 i).differentiable (by norm_num)

lemma ind_form (E : Economy) (i : Fin 2) (c K : ℝ) :
    (fun v => if c ≤ v then K * E.dens i v else 0) = (Ici c).indicator (fun v => K * E.dens i v) := by
  ext v; simp [Set.indicator_apply, mem_Ici]

lemma int_tail (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (c : ℝ)
    (hc : c ∈ E.V) (K : ℝ) :
    ∫ v in E.V, (if c ≤ v then K * E.dens i v else 0) = K * E.D i c := by
  rw [ind_form, setIntegral_indicator measurableSet_Ici]
  have hset : E.V ∩ Ici c = Icc c E.vhi := by
    ext v; simp only [Economy.V, mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨le_trans hc.1 h3, h2⟩, h3⟩
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc.2,
    intervalIntegral.integral_const_mul]
  unfold Economy.dens
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => D_diff E h1 i x)
    (((h1.1 i).continuous_deriv (by norm_num)).intervalIntegrable _ _), hE.D_vhi i]
  ring

lemma integrable_tail (E : Economy) (h1 : E.Condition1) (i : Fin 2) (c K : ℝ) :
    IntegrableOn (fun v => if c ≤ v then K * E.dens i v else 0) E.V := by
  rw [ind_form]
  exact (((continuous_const.mul (dens_cont E h1 i)).integrableOn_Icc)).indicator measurableSet_Ici

lemma profit_sbsmp (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (a b : ℝ)
    (ha : a ∈ E.V) (hb : b ∈ E.V) :
    E.profit (sbsmp a b) = E.α₁ * E.D 0 a * a + (1 - E.α₁) * E.D 1 b * b := by
  unfold Economy.profit
  have hfun : (fun v => ∑ i, (sbsmp a b).t i v * ind ((sbsmp a b).x i v) * E.prob i * E.dens i v)
      = fun v => (if a ≤ v then (a * E.α₁) * E.dens 0 v else 0) +
          (if b ≤ v then (b * (1 - E.α₁)) * E.dens 1 v else 0) := by
    ext v
    simp only [Fin.sum_univ_two, sbsmp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Economy.prob, ind]
    split_ifs <;> simp_all
  rw [hfun, integral_add (integrable_tail E h1 0 a _) (integrable_tail E h1 1 b _),
    int_tail E hE h1 0 a ha, int_tail E hE h1 1 b hb]
  ring

lemma rev_strictConcave (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h3 : E.Condition3)
    (i : Fin 2) : StrictConcaveOn ℝ E.V (fun p => p * E.D i p) := by
  have hD := D_diff E h1 i
  have hD' : Differentiable ℝ (deriv (E.D i)) :=
    ((h1.1 i).deriv' (n := 1)).differentiable (by norm_num)
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
  · exact (continuous_id.mul (hD.continuous)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hxV : x ∈ E.V := Ioo_subset_Icc_self hx
    have e1 : deriv (fun p => p * E.D i p) = fun p => E.D i p + p * deriv (E.D i) p := by
      ext p
      have := (hasDerivAt_id p).mul (hD p).hasDerivAt
      simp only [id, one_mul] at this
      exact this.deriv
    have e2 : deriv (fun p => E.D i p + p * deriv (E.D i) p) x =
        deriv (E.D i) x + (deriv (E.D i) x + x * deriv (deriv (E.D i)) x) := by
      have := (hD x).hasDerivAt.add ((hasDerivAt_id x).mul (hD' x).hasDerivAt)
      simp only [id, one_mul] at this
      exact this.deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [e1, e2]
    have := h1.2 i x hxV
    have := h3 i x hxV
    have hx0 : 0 < x := lt_of_le_of_lt hE.vlo_nonneg hx.1
    nlinarith

lemma unique_max (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h3 : E.Condition3)
    (i : Fin 2) (p a : ℝ) (hp : E.IsMonopolyPrice i p) (ha : a ∈ E.V)
    (heq : a * E.D i a = p * E.D i p) : a = p := by
  by_contra hne
  have hsc := rev_strictConcave E hE h1 h3 i
  have := hsc.2 ha hp.1 hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hmid : (1/2 : ℝ) • a + (1/2 : ℝ) • p ∈ E.V := (convex_Icc _ _) ha hp.1 (by norm_num)
    (by norm_num) (by norm_num)
  have := hp.2 _ hmid
  simp only [smul_eq_mul] at *
  linarith

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
  have hw0 : 0 ≤ E.prob 0 * E.dens 0 v := by
    have : 0 < E.dens 0 v := by unfold Economy.dens; linarith [h1.2 0 v hv]
    have : 0 < E.prob 0 := by simp [Economy.prob]; linarith [hE.α₁_pos]
    positivity
  have hw1 : 0 ≤ E.prob 1 * E.dens 1 v := by
    have : 0 < E.dens 1 v := by unfold Economy.dens; linarith [h1.2 1 v hv]
    have : 0 < E.prob 1 := by simp [Economy.prob]; linarith [hE.α₁_lt_one]
    positivity
  unfold Economy.payoff
  simp only [Fin.sum_univ_two, sbsmp, Matrix.cons_val_zero, Matrix.cons_val_one]
  have t0 := term_le a v vhat _ hw0
  have t1 := term_le b v vhat _ hw1
  simp only [mul_assoc] at t0 t1 ⊢
  linarith

end Aux_MDU_A57

open MonopolyDemandUncertainty.SBSMP Aux_MDU_A57 in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h3 : E.Condition3)
    (p₁ p₂ : ℝ) (hp₁ : E.IsMonopolyPrice 0 p₁) (hp₂ : E.IsMonopolyPrice 1 p₂) :
    (∀ a ∈ E.V, ∀ b ∈ E.V,
        E.profit (sbsmp a b) = E.α₁ * E.D 0 a * a + (1 - E.α₁) * E.D 1 b * b) ∧
      (∀ a ∈ E.V, ∀ b ∈ E.V, E.profit (sbsmp a b) ≤ E.profit (sbsmp p₁ p₂) ∧
        (E.profit (sbsmp a b) = E.profit (sbsmp p₁ p₂) → a = p₁ ∧ b = p₂)) ∧
      E.IsBIC (sbsmp p₁ p₂) ∧ E.IsEIR (sbsmp p₁ p₂) := by
  refine ⟨fun a ha b hb => profit_sbsmp E hE h1 a b ha hb, ?_, sbsmp_BIC E hE h1 p₁ p₂,
    sbsmp_EIR E hE p₁ p₂ hp₁.1 hp₂.1⟩
  intro a ha b hb
  rw [profit_sbsmp E hE h1 a b ha hb, profit_sbsmp E hE h1 p₁ p₂ hp₁.1 hp₂.1]
  have e1 := hp₁.2 a ha
  have e2 := hp₂.2 b hb
  have hα : 0 < E.α₁ := hE.α₁_pos
  have hα' : 0 < 1 - E.α₁ := by linarith [hE.α₁_lt_one]
  have m1 := mul_le_mul_of_nonneg_left e1 hα.le
  have m2 := mul_le_mul_of_nonneg_left e2 hα'.le
  refine ⟨by nlinarith, fun heq => ?_⟩
  have q1 : a * E.D 0 a = p₁ * E.D 0 p₁ := by
    by_contra hne
    have hlt : a * E.D 0 a < p₁ * E.D 0 p₁ := lt_of_le_of_ne e1 hne
    have := mul_lt_mul_of_pos_left hlt hα
    nlinarith
  have q2 : b * E.D 1 b = p₂ * E.D 1 p₂ := by
    by_contra hne
    have hlt : b * E.D 1 b < p₂ * E.D 1 p₂ := lt_of_le_of_ne e2 hne
    have := mul_lt_mul_of_pos_left hlt hα'
    nlinarith
  exact ⟨unique_max E hE h1 h3 0 p₁ a hp₁ ha q1, unique_max E hE h1 h3 1 p₂ b hp₂ hb q2⟩
