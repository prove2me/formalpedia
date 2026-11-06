-- Prove2me | solution 1 for LinParamBandits.LowerBound.norm_prob_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:30:50.530581+00:00
-- url     : https://prove2.me/submissions/0d3b06c9-0bd8-4b03-a33c-755cd63bb692

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

open MeasureTheory ProbabilityTheory

namespace LPB24Aux
open LinParamBandits.LowerBound

lemma gauss_sq : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

lemma gauss_exp (a : ℝ) (ha : 0 < a) :
    ∫ x, Real.exp (-a * x ^ 2) ∂(gaussianReal 0 1) = Real.sqrt (1 / (1 + 2 * a)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
  have : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a + 1 / 2) * x ^ 2) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_gaussian, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  have hpi := Real.pi_pos
  field_simp
  ring

/-- The map `y ↦ y / √r` from the coordinate space to `Vec r`. -/
noncomputable def F (r : ℕ) (y : Fin r → ℝ) : Vec r := (Real.sqrt r)⁻¹ • WithLp.toLp 2 y

lemma measurable_F (r : ℕ) : Measurable (F r) := by unfold F; fun_prop

lemma prior_eq (r : ℕ) :
    prior r = (Measure.pi (fun _ : Fin r => gaussianReal 0 1)).map (F r) := by
  unfold prior
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma norm_F_sq (r : ℕ) (hr : 1 ≤ r) (y : Fin r → ℝ) :
    ‖F r y‖ ^ 2 = (∑ i, y i ^ 2) / r := by
  unfold F
  rw [norm_smul, mul_pow, EuclideanSpace.real_norm_sq_eq]
  have : (0 : ℝ) < r := by exact_mod_cast hr
  rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt this.le]
  simp [div_eq_inv_mul]

end LPB24Aux

open LinParamBandits.LowerBound LPB24Aux in
theorem solution (r : ℕ) (hr : 2 ≤ r) (θ β : ℝ) (hθ : θ ≤ 1 / 2) (hβ : 0 < β) :
    1 - 4 * θ ^ 2 - 1 / β ^ 2 ≤ (prior r).real {z | θ ≤ ‖z‖ ∧ ‖z‖ ≤ β} := by
  set μ := Measure.pi (fun _ : Fin r => gaussianReal 0 1) with hμ
  have hν := prior_eq r
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  haveI : IsProbabilityMeasure (prior r) := by
    rw [hν]; exact Measure.isProbabilityMeasure_map (measurable_F r).aemeasurable
  -- integrability of coordinates squared
  have hint_i : ∀ i : Fin r, Integrable (fun y : Fin r → ℝ => y i ^ 2) μ := by
    intro i
    have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    exact (measurePreserving_eval (fun _ : Fin r => gaussianReal 0 1) i).integrable_comp_of_integrable h2
  -- second moment
  have hint2 : Integrable (fun z : Vec r => ‖z‖ ^ 2) (prior r) := by
    rw [hν, integrable_map_measure (by fun_prop) (measurable_F r).aemeasurable]
    have : ((fun z : Vec r => ‖z‖ ^ 2) ∘ F r) = fun y : Fin r → ℝ => (∑ i, y i ^ 2) / r := by
      funext y; simp [norm_F_sq r (by omega) y]
    rw [this]
    exact (integrable_finset_sum _ (fun i _ => hint_i i)).div_const _
  have hmom : ∫ z, ‖z‖ ^ 2 ∂(prior r) = 1 := by
    rw [hν, integral_map (measurable_F r).aemeasurable (by fun_prop)]
    simp_rw [norm_F_sq r (by omega)]
    rw [integral_div, integral_finset_sum _ (fun i _ => hint_i i)]
    have : ∀ i : Fin r, ∫ y : Fin r → ℝ, y i ^ 2 ∂μ = 1 := by
      intro i
      have h := integral_comp_eval (μ := fun _ : Fin r => gaussianReal 0 1) (i := i)
        (f := fun x : ℝ => x ^ 2) (by fun_prop)
      exact h.trans gauss_sq
    simp_rw [this]
    simp [hr0.ne', (by omega : r ≠ 0)]
  -- upper tail
  set U := {z : Vec r | β < ‖z‖} with hU
  have hUle : (prior r).real U ≤ 1 / β ^ 2 := by
    have hsub : U ⊆ {z | β ^ 2 ≤ ‖z‖ ^ 2} := by
      intro z hz
      simp only [hU, Set.mem_setOf_eq] at hz ⊢
      nlinarith
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := prior r)
      (Filter.Eventually.of_forall (fun z => by positivity)) hint2 (β ^ 2)
    rw [hmom] at hm
    have h1 : (prior r).real U ≤ (prior r).real {z | β ^ 2 ≤ ‖z‖ ^ 2} := measureReal_mono hsub
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- lower tail
  set L := {z : Vec r | ‖z‖ < θ} with hL
  have hLle : (prior r).real L ≤ 4 * θ ^ 2 := by
    rcases le_or_gt θ 0 with h0 | h0
    · have : L = ∅ := by
        ext z; simp only [hL, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact le_trans h0 (norm_nonneg z)
      rw [this]; simp; positivity
    · set c : ℝ := r / θ ^ 2 with hc
      have hcpos : 0 < c := by positivity
      have hsub : L ⊆ {z | Real.exp (-c * θ ^ 2) ≤ Real.exp (-c * ‖z‖ ^ 2)} := by
        intro z hz
        simp only [hL, Set.mem_setOf_eq] at hz ⊢
        apply Real.exp_le_exp.mpr
        have : ‖z‖ ^ 2 ≤ θ ^ 2 := by nlinarith [norm_nonneg z]
        nlinarith
      have hintE : Integrable (fun z : Vec r => Real.exp (-c * ‖z‖ ^ 2)) (prior r) := by
        refine Integrable.of_bound (C := 1) (by fun_prop) (Filter.Eventually.of_forall ?_)
        intro z
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_one_iff.mpr
        nlinarith [sq_nonneg ‖z‖]
      have hm := mul_meas_ge_le_integral_of_nonneg (μ := prior r)
        (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le)) hintE (Real.exp (-c * θ ^ 2))
      -- compute the integral
      set s : ℝ := Real.sqrt (1 / (1 + 2 * (1 / θ ^ 2))) with hs
      have hE : ∫ z, Real.exp (-c * ‖z‖ ^ 2) ∂(prior r) = s ^ r := by
        rw [hν, integral_map (measurable_F r).aemeasurable (by fun_prop)]
        have : ∀ y : Fin r → ℝ, Real.exp (-c * ‖F r y‖ ^ 2)
            = ∏ i, Real.exp (-(1 / θ ^ 2) * y i ^ 2) := by
          intro y
          rw [norm_F_sq r (by omega), ← Real.exp_sum]
          congr 1
          rw [hc, Finset.sum_div, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          field_simp
        simp_rw [this]
        rw [integral_fintype_prod_eq_prod (f := fun _ x => Real.exp (-(1 / θ ^ 2) * x ^ 2))]
        rw [gauss_exp _ (by positivity), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hE] at hm
      have hexp : Real.exp (-c * θ ^ 2) = Real.exp (-r) := by
        congr 1; rw [hc]; field_simp
      rw [hexp] at hm
      have h1 : (prior r).real L ≤ (prior r).real
          {z | Real.exp (-c * θ ^ 2) ≤ Real.exp (-c * ‖z‖ ^ 2)} := measureReal_mono hsub
      have hL2 : (prior r).real L ≤ (Real.exp 1 * s) ^ r := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one]
        rw [hexp] at h1
        have : Real.exp (r : ℝ) * Real.exp (-(r : ℝ)) = 1 := by
          rw [← Real.exp_add]; simp
        calc (prior r).real L
            ≤ (prior r).real {z | Real.exp (-(r : ℝ)) ≤ Real.exp (-c * ‖z‖ ^ 2)} := h1
          _ = Real.exp r * (Real.exp (-(r : ℝ)) *
              (prior r).real {z | Real.exp (-(r : ℝ)) ≤ Real.exp (-c * ‖z‖ ^ 2)}) := by
              rw [← mul_assoc, this, one_mul]
          _ ≤ Real.exp r * s ^ r := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      -- numerics
      have hs2 : s ^ 2 = θ ^ 2 / (θ ^ 2 + 2) := by
        rw [hs, Real.sq_sqrt (by positivity)]
        field_simp
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have he0 : 0 < Real.exp 1 := Real.exp_pos 1
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hq2 : (Real.exp 1 * s) ^ 2 = Real.exp 1 ^ 2 * θ ^ 2 / (θ ^ 2 + 2) := by
        rw [mul_pow, hs2]; ring
      have hq2le : (Real.exp 1 * s) ^ 2 ≤ 4 * θ ^ 2 := by
        rw [hq2, div_le_iff₀ (by positivity)]
        have he2 : Real.exp 1 ^ 2 < 8 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right he2.le (sq_nonneg θ), sq_nonneg θ,
          mul_nonneg (sq_nonneg θ) (sq_nonneg θ)]
      have hq1 : Real.exp 1 * s ≤ 1 := by
        have : (Real.exp 1 * s) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_nonneg he0.le hs0]
      have hqr : (Real.exp 1 * s) ^ r ≤ (Real.exp 1 * s) ^ 2 :=
        pow_le_pow_of_le_one (by positivity) hq1 hr
      linarith
  -- combine
  have hcover : (Set.univ : Set (Vec r)) ⊆ ({z | θ ≤ ‖z‖ ∧ ‖z‖ ≤ β} ∪ L) ∪ U := by
    intro z _
    simp only [hL, hU, Set.mem_union, Set.mem_setOf_eq]
    by_cases h1 : θ ≤ ‖z‖
    · by_cases h2 : ‖z‖ ≤ β
      · left; left; exact ⟨h1, h2⟩
      · right; linarith [not_le.mp h2]
    · left; right; exact not_le.mp h1
  have h1 := measureReal_mono (μ := prior r) hcover
  have h2 := measureReal_union_le (μ := prior r) ({z : Vec r | θ ≤ ‖z‖ ∧ ‖z‖ ≤ β} ∪ L) U
  have h3 := measureReal_union_le (μ := prior r) {z : Vec r | θ ≤ ‖z‖ ∧ ‖z‖ ≤ β} L
  rw [probReal_univ] at h1
  linarith
