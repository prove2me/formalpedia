-- Prove2me | solution 1 for Newton.lintegral_mul_mul_le_three_holder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:09.164861+00:00
-- url     : https://prove2.me/submissions/43ea116c-0ca9-40b3-9260-155537c3248c

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ≥0∞}
    {p q r : ℝ≥0∞}
    (hpqr : 1 / p + 1 / q + 1 / r = 1)
    (hp_top : p ≠ ⊤) (hq_top : q ≠ ⊤) (hr_top : r ≠ ⊤)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) :
    ∫⁻ x, f x * g x * h x ∂μ ≤
      (∫⁻ x, f x ^ p.toReal ∂μ) ^ (1/p.toReal) *
      (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1/q.toReal) *
      (∫⁻ x, h x ^ r.toReal ∂μ) ^ (1/r.toReal) := by
  have hp_pos : 0 < p := by
    by_contra h_neg
    push_neg at h_neg
    have : p = 0 := le_antisymm h_neg zero_le
    simp [this] at hpqr
  have hq_pos : 0 < q := by
    by_contra h_neg
    push_neg at h_neg
    have : q = 0 := le_antisymm h_neg zero_le
    simp [this] at hpqr
  have hr_pos : 0 < r := by
    by_contra h_neg
    push_neg at h_neg
    have : r = 0 := le_antisymm h_neg zero_le
    simp [this] at hpqr
  -- Convert to real numbers
  have hp_real_pos : 0 < p.toReal := ENNReal.toReal_pos hp_pos.ne' hp_top
  have hq_real_pos : 0 < q.toReal := ENNReal.toReal_pos hq_pos.ne' hq_top
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr_pos.ne' hr_top
  -- Finiteness lemmas
  have h_finite_p : 1/p ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hp_pos.ne'
  have h_finite_q : 1/q ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hq_pos.ne'
  have h_finite_r : 1/r ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hr_pos.ne'
  -- Convert exponent condition to real numbers
  have hpqr_real : 1/p.toReal + 1/q.toReal + 1/r.toReal = 1 := by
    have h1 : (1/p).toReal = 1/p.toReal := ENNReal.toReal_div 1 p
    have h2 : (1/q).toReal = 1/q.toReal := ENNReal.toReal_div 1 q
    have h3 : (1/r).toReal = 1/r.toReal := ENNReal.toReal_div 1 r
    have h_pq_ne_top : 1/p + 1/q ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h_finite_p, h_finite_q⟩
    have h_sum : (1/p + 1/q + 1/r).toReal = 1 := by
      have : 1/p + 1/q + 1/r = 1 := hpqr
      rw [this, ENNReal.toReal_one]
    calc 1/p.toReal + 1/q.toReal + 1/r.toReal
        = (1/p).toReal + (1/q).toReal + (1/r).toReal := by rw [h1, h2, h3]
      _ = ((1/p) + (1/q)).toReal + (1/r).toReal := by
          rw [ENNReal.toReal_add h_finite_p h_finite_q]
      _ = ((1/p + 1/q) + (1/r)).toReal := by
          rw [ENNReal.toReal_add h_pq_ne_top h_finite_r]
      _ = 1 := h_sum
  let F : α → ℝ≥0∞ := fun x => (f x) ^ p.toReal
  let G : α → ℝ≥0∞ := fun x => (g x) ^ q.toReal
  let H : α → ℝ≥0∞ := fun x => (h x) ^ r.toReal
  have hF : AEMeasurable F μ := hf.pow_const p.toReal
  have hG : AEMeasurable G μ := hg.pow_const q.toReal
  have hH : AEMeasurable H μ := hh.pow_const r.toReal
  -- Lemma showing (f^p)^(1/p) = f
  have rpow_inv_cancel : ∀ (a : ℝ≥0∞) (t : ℝ), 0 < t → (a ^ t) ^ (1/t) = a := by
    intro a t ht
    rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
  -- Show f * g * h = F^(1/p) * G^(1/q) * H^(1/r)
  have h_eq : ∀ x, f x * g x * h x =
      F x ^ (1/p.toReal) * G x ^ (1/q.toReal) * H x ^ (1/r.toReal) := by
    intro x
    simp only [F, G, H]
    rw [rpow_inv_cancel (f x) p.toReal hp_real_pos,
        rpow_inv_cancel (g x) q.toReal hq_real_pos,
        rpow_inv_cancel (h x) r.toReal hr_real_pos]
  -- Apply lintegral_prod_norm_pow_le using Finset.univ (Fin 3)
  let s : Finset (Fin 3) := Finset.univ
  let funcs : Fin 3 → α → ℝ≥0∞ := ![F, G, H]
  let exps : Fin 3 → ℝ := ![1/p.toReal, 1/q.toReal, 1/r.toReal]
  have h_meas : ∀ i ∈ s, AEMeasurable (funcs i) μ := by
    intro i _
    fin_cases i
    · exact hF
    · exact hG
    · exact hH
  have h_sum_exp : ∑ i ∈ s, exps i = 1 := by
    simp only [s, exps]
    rw [Fin.sum_univ_three]
    exact hpqr_real
  have h_nonneg : ∀ i ∈ s, 0 ≤ exps i := by
    intro i _
    fin_cases i
    · exact (one_div_pos.2 hp_real_pos).le
    · exact (one_div_pos.2 hq_real_pos).le
    · exact (one_div_pos.2 hr_real_pos).le
  have h_prod := ENNReal.lintegral_prod_norm_pow_le s h_meas h_sum_exp h_nonneg
  -- Transform to get the conclusion
  have h_lhs_eq : ∀ x, ∏ i ∈ s, funcs i x ^ exps i =
      F x ^ (1/p.toReal) * G x ^ (1/q.toReal) * H x ^ (1/r.toReal) := by
    intro x
    simp only [s, funcs, exps]
    rw [Fin.prod_univ_three]
    rfl
  have h_rhs_eq : ∏ i ∈ s, (∫⁻ x, funcs i x ∂μ) ^ exps i =
      (∫⁻ x, F x ∂μ) ^ (1/p.toReal) * (∫⁻ x, G x ∂μ) ^ (1/q.toReal) *
      (∫⁻ x, H x ∂μ) ^ (1/r.toReal) := by
    simp only [s, funcs, exps]
    rw [Fin.prod_univ_three]
    rfl
  calc ∫⁻ x, f x * g x * h x ∂μ
      = ∫⁻ x, F x ^ (1/p.toReal) * G x ^ (1/q.toReal) * H x ^ (1/r.toReal) ∂μ := by
        congr 1; ext x; exact h_eq x
    _ = ∫⁻ x, ∏ i ∈ s, funcs i x ^ exps i ∂μ := by
        congr 1; ext x; exact (h_lhs_eq x).symm
    _ ≤ ∏ i ∈ s, (∫⁻ x, funcs i x ∂μ) ^ exps i := h_prod
    _ = (∫⁻ x, F x ∂μ) ^ (1/p.toReal) * (∫⁻ x, G x ∂μ) ^ (1/q.toReal) *
        (∫⁻ x, H x ∂μ) ^ (1/r.toReal) := h_rhs_eq
    _ = (∫⁻ x, f x ^ p.toReal ∂μ) ^ (1/p.toReal) * (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1/q.toReal) *
        (∫⁻ x, h x ^ r.toReal ∂μ) ^ (1/r.toReal) := by rfl
end Newton
