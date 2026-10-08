-- Prove2me | solution 1 for MassartDKW.Tight.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:40:08.391463+00:00
-- url     : https://prove2.me/submissions/9e0dae51-5630-43f9-b5a4-a01a0da21243

import Mathlib



namespace MassartDKW.Tight

open MeasureTheory intervalIntegral Set

/-- Elementary bound `1/(σ+w) + 1/(σ-w) ≤ 2/σ + 2w²/(σ(σ²-δ²))` for `w² ≤ δ² < σ²`. -/
lemma frac_bound (σ w δ : ℝ) (hδ : 0 < δ) (hσ : δ < σ) (hw : w ^ 2 ≤ δ ^ 2) :
    1 / (σ + w) + 1 / (σ - w) ≤ 2 / σ + 2 * w ^ 2 / (σ * (σ ^ 2 - δ ^ 2)) := by
  have hσ0 : 0 < σ := by linarith
  have hwa : w ^ 2 < σ ^ 2 := by nlinarith
  have h1 : 0 < σ + w := by nlinarith [sq_nonneg (σ - w), sq_nonneg (σ + w)]
  have h2 : 0 < σ - w := by nlinarith [sq_nonneg (σ - w), sq_nonneg (σ + w)]
  have hQ : 0 < σ ^ 2 - δ ^ 2 := by nlinarith
  have hP : 0 < (σ + w) * (σ - w) := mul_pos h1 h2
  have key : 2 / σ + 2 * w ^ 2 / (σ * (σ ^ 2 - δ ^ 2)) - (1 / (σ + w) + 1 / (σ - w))
      = 2 * w ^ 2 * (δ ^ 2 - w ^ 2) / (σ * (σ ^ 2 - δ ^ 2) * ((σ + w) * (σ - w))) := by
    field_simp
    ring
  have : 0 ≤ 2 * w ^ 2 * (δ ^ 2 - w ^ 2) / (σ * (σ ^ 2 - δ ^ 2) * ((σ + w) * (σ - w))) := by
    apply div_nonneg
    · have := sub_nonneg.mpr hw; positivity
    · positivity
  linarith

/-- AM–GM in the form `m² ≤ p q → 2 m ≤ p + q` for nonnegative numbers. -/
lemma two_mul_le_add_of_sq_le {p q m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 ≤ m)
    (h : m ^ 2 ≤ p * q) : 2 * m ≤ p + q := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + q - 2 * m)]

theorem lemma_3_core (δ s : ℝ) (hδ : 0 < δ) (hδs : δ < s) (hs1 : s < 1 - δ) (g : ℝ → ℝ)
    (hg : ∀ u ∈ Set.Icc (s - δ) (s + δ), 0 < g u)
    (hlog : ConvexOn ℝ (Set.Icc (s - δ) (s + δ)) (fun u => Real.log (g u))) (l : ℝ) (hl : 0 < l) :
    g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s))) *
        Real.exp (-(l ^ 2 * δ ^ 2 / 6) *
          ((s * (s ^ 2 - δ ^ 2))⁻¹ + ((1 - s) * ((1 - s) ^ 2 - δ ^ 2))⁻¹)) ≤
      1 / (2 * δ) * ∫ u in (s - δ)..(s + δ), g u * Real.exp (-(l ^ 2) / (2 * u * (1 - u))) := by
  set a := s - δ with ha
  set b := s + δ with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb1 : b < 1 := by rw [hb]; linarith
  set K : ℝ → ℝ := fun u => Real.exp (-(l ^ 2) / (2 * u * (1 - u))) with hK
  set h : ℝ → ℝ := fun u => g u * K u with hh
  have hs_mem : s ∈ Icc a b := ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩
  ------------------------------------------------------------------
  -- Part A : integrability of h on [a, b]
  ------------------------------------------------------------------
  have hlogc : ContinuousOn (fun u => Real.log (g u)) (Ioo a b) := by
    have := hlog.continuousOn_interior
    rwa [interior_Icc] at this
  have hgc : ContinuousOn g (Ioo a b) := by
    refine (Real.continuous_exp.comp_continuousOn hlogc).congr ?_
    intro u hu
    simp only [Function.comp]
    rw [Real.exp_log (hg u (Ioo_subset_Icc_self hu))]
  have hKc : ContinuousOn K (Ioo a b) := by
    rw [hK]
    apply ContinuousOn.rexp
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    have h1 : 0 < u := by linarith [hu.1]
    have h2 : 0 < 1 - u := by linarith [hu.2]
    positivity
  set M : ℝ := Real.exp (max (Real.log (g a)) (Real.log (g b))) with hM
  have hbound : ∀ u ∈ Icc a b, ‖h u‖ ≤ M := by
    intro u hu
    have hgu := hg u hu
    have hKu : 0 < K u := Real.exp_pos _
    have hKle : K u ≤ 1 := by
      rw [hK]; simp only
      rw [Real.exp_le_one_iff]
      have h1 : 0 < u := by linarith [hu.1]
      have h2 : 0 < 1 - u := by linarith [hu.2]
      apply div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    have hgle : g u ≤ M := by
      have hseg : u ∈ segment ℝ a b := by rw [segment_eq_Icc hab]; exact hu
      have := hlog.le_on_segment (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hseg
      rw [hM, ← Real.exp_log hgu]
      exact Real.exp_le_exp.mpr this
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hgu hKu)]
    calc g u * K u ≤ g u * 1 := by apply mul_le_mul_of_nonneg_left hKle hgu.le
      _ = g u := mul_one _
      _ ≤ M := hgle
  have hint : IntervalIntegrable h volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, integrableOn_Ioc_iff_integrableOn_Ioo]
    refine ⟨(hgc.mul hKc).aestronglyMeasurable measurableSet_Ioo, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := M)
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun u hu => hbound u (Ioo_subset_Icc_self hu))
  ------------------------------------------------------------------
  -- Part B : the pointwise bound
  ------------------------------------------------------------------
  set A : ℝ := (s * (s ^ 2 - δ ^ 2))⁻¹ with hA
  set B : ℝ := ((1 - s) * ((1 - s) ^ 2 - δ ^ 2))⁻¹ with hB
  set c : ℝ := l ^ 2 * δ ^ 2 / 2 * (A + B) with hc
  set E0 : ℝ := Real.exp (-(l ^ 2) / (2 * s * (1 - s))) with hE0
  have hs0 : 0 < s := by linarith
  have hs1' : 0 < 1 - s := by linarith
  have hApos : 0 < A := by rw [hA]; apply inv_pos.mpr; apply mul_pos hs0; nlinarith
  have hBpos : 0 < B := by rw [hB]; apply inv_pos.mpr; apply mul_pos hs1'; nlinarith
  have hgs := hg s hs_mem
  set lower : ℝ → ℝ := fun u =>
    2 * g s * E0 * Real.exp (-c / 3) * (1 - c * ((u - s) ^ 2 / δ ^ 2 - 1 / 3)) with hlower
  have hpt : ∀ u ∈ Icc a b, lower u ≤ h u + h (2 * s - u) := by
    intro u hu
    set w := u - s with hw
    have hu' : 2 * s - u ∈ Icc a b := ⟨by rw [ha]; linarith [hu.2], by rw [hb]; linarith [hu.1]⟩
    have hw2 : w ^ 2 ≤ δ ^ 2 := by
      rw [hw]; nlinarith [hu.1, hu.2]
    -- (i) convexity of log g
    have hgg : g s ^ 2 ≤ g u * g (2 * s - u) := by
      have := hlog.2 hu hu' (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at this
      rw [show 1 / 2 * u + 1 / 2 * (2 * s - u) = s by ring] at this
      have e1 : g s ^ 2 = Real.exp (2 * Real.log (g s)) := by
        rw [show (2:ℝ) * Real.log (g s) = ((2:ℕ):ℝ) * Real.log (g s) by norm_num, Real.exp_nat_mul,
          Real.exp_log hgs]
      have e2 : g u * g (2 * s - u) = Real.exp (Real.log (g u) + Real.log (g (2 * s - u))) := by
        rw [Real.exp_add, Real.exp_log (hg u hu), Real.exp_log (hg _ hu')]
      rw [e1, e2]
      apply Real.exp_le_exp.mpr
      linarith
    -- (ii) the exponential factor
    have hu0 : 0 < u := by linarith [hu.1]
    have hu1 : 0 < 1 - u := by linarith [hu.2]
    have hu0' : 0 < 2 * s - u := by linarith [hu'.1]
    have hu1' : 0 < 1 - (2 * s - u) := by linarith [hu'.2]
    have hKK : Real.exp (2 * (-(l ^ 2) / (2 * s * (1 - s))) - 2 * c * w ^ 2 / δ ^ 2)
        ≤ K u * K (2 * s - u) := by
      rw [hK]; simp only
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have f1 := frac_bound s w δ hδ hδs hw2
      have f2 := frac_bound (1 - s) (-w) δ hδ (by linarith) (by rw [neg_sq]; exact hw2)
      rw [show s + w = u by rw [hw]; ring, show s - w = 2 * s - u by rw [hw]; ring] at f1
      rw [show 1 - s + -w = 1 - u by rw [hw]; ring, show 1 - s - -w = 1 - (2 * s - u) by rw [hw]; ring,
        neg_sq] at f2
      have eq1 : -(l ^ 2) / (2 * u * (1 - u)) + -(l ^ 2) / (2 * (2 * s - u) * (1 - (2 * s - u)))
          = -(l ^ 2) / 2 * ((1 / u + 1 / (2 * s - u)) + (1 / (1 - u) + 1 / (1 - (2 * s - u)))) := by
        field_simp
        ring
      have eq2 : 2 * (-(l ^ 2) / (2 * s * (1 - s))) - 2 * c * w ^ 2 / δ ^ 2
          = -(l ^ 2) / 2 * ((2 / s + 2 * w ^ 2 / (s * (s ^ 2 - δ ^ 2)))
              + (2 / (1 - s) + 2 * w ^ 2 / ((1 - s) * ((1 - s) ^ 2 - δ ^ 2)))) := by
        rw [hc, hA, hB]
        field_simp
        ring
      rw [eq1, eq2]
      apply mul_le_mul_of_nonpos_left _ (by have := sq_nonneg l; linarith)
      linarith
    -- (iii) combine
    have hprod : (g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s)) - c * w ^ 2 / δ ^ 2)) ^ 2
        ≤ h u * h (2 * s - u) := by
      rw [hh]; simp only
      rw [mul_pow, show (Real.exp (-(l ^ 2) / (2 * s * (1 - s)) - c * w ^ 2 / δ ^ 2)) ^ 2
          = Real.exp (2 * (-(l ^ 2) / (2 * s * (1 - s))) - 2 * c * w ^ 2 / δ ^ 2) by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
      calc g s ^ 2 * Real.exp (2 * (-(l ^ 2) / (2 * s * (1 - s))) - 2 * c * w ^ 2 / δ ^ 2)
          ≤ (g u * g (2 * s - u)) * (K u * K (2 * s - u)) := by
            apply mul_le_mul hgg hKK (Real.exp_pos _).le
            exact mul_nonneg (hg u hu).le (hg _ hu').le
        _ = g u * K u * (g (2 * s - u) * K (2 * s - u)) := by ring
    have hamgm := two_mul_le_add_of_sq_le (mul_nonneg (hg u hu).le (Real.exp_pos _).le)
      (mul_nonneg (hg _ hu').le (Real.exp_pos _).le)
      (mul_nonneg hgs.le (Real.exp_pos _).le) hprod
    -- tangent line bound for the exponential
    have htan : E0 * Real.exp (-c / 3) * (1 - c * (w ^ 2 / δ ^ 2 - 1 / 3))
        ≤ Real.exp (-(l ^ 2) / (2 * s * (1 - s)) - c * w ^ 2 / δ ^ 2) := by
      rw [hE0, ← Real.exp_add]
      have := Real.add_one_le_exp (-c * (w ^ 2 / δ ^ 2 - 1 / 3))
      calc Real.exp (-(l ^ 2) / (2 * s * (1 - s)) + -c / 3) * (1 - c * (w ^ 2 / δ ^ 2 - 1 / 3))
          ≤ Real.exp (-(l ^ 2) / (2 * s * (1 - s)) + -c / 3) * Real.exp (-c * (w ^ 2 / δ ^ 2 - 1 / 3)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            linarith
        _ = Real.exp (-(l ^ 2) / (2 * s * (1 - s)) - c * w ^ 2 / δ ^ 2) := by
            rw [← Real.exp_add]; congr 1; ring
    rw [hlower]; simp only
    rw [hw] at htan
    have hgs2 : 0 ≤ 2 * g s := by linarith
    calc 2 * g s * E0 * Real.exp (-c / 3) * (1 - c * ((u - s) ^ 2 / δ ^ 2 - 1 / 3))
        = 2 * g s * (E0 * Real.exp (-c / 3) * (1 - c * ((u - s) ^ 2 / δ ^ 2 - 1 / 3))) := by ring
      _ ≤ 2 * g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s)) - c * (u - s) ^ 2 / δ ^ 2) :=
          mul_le_mul_of_nonneg_left htan hgs2
      _ = 2 * (g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s)) - c * (u - s) ^ 2 / δ ^ 2)) := by ring
      _ ≤ h u + h (2 * s - u) := by rw [hw] at hamgm; exact hamgm
  ------------------------------------------------------------------
  -- Part C : integrate
  ------------------------------------------------------------------
  have hint' : IntervalIntegrable (fun u => h (2 * s - u)) volume a b := by
    have := hint.comp_sub_left (2 * s)
    rw [show 2 * s - a = b by rw [ha, hb]; ring, show 2 * s - b = a by rw [ha, hb]; ring] at this
    exact this.symm
  have hlowint : IntervalIntegrable lower volume a b := by
    apply Continuous.intervalIntegrable
    rw [hlower]; fun_prop
  have hrefl : ∫ u in a..b, h (2 * s - u) = ∫ u in a..b, h u := by
    rw [intervalIntegral.integral_comp_sub_left h (2 * s)]
    rw [show 2 * s - a = b by rw [ha, hb]; ring, show 2 * s - b = a by rw [ha, hb]; ring]
  have hlowval : ∫ u in a..b, lower u = 2 * g s * E0 * Real.exp (-c / 3) * (2 * δ) := by
    have hderiv : ∀ u, HasDerivAt (fun u => 2 * g s * E0 * Real.exp (-c / 3) *
        (u - c * ((u - s) ^ 3 / (3 * δ ^ 2) - u / 3))) (lower u) u := by
      intro u
      rw [hlower]; simp only
      have h1 := ((((hasDerivAt_id u).sub_const s).pow 3).div_const (3 * δ ^ 2)).sub
        ((hasDerivAt_id u).div_const 3)
      have h2 := ((hasDerivAt_id u).sub (h1.const_mul c)).const_mul (2 * g s * E0 * Real.exp (-c / 3))
      refine h2.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hlowint]
    rw [ha, hb]
    field_simp
    ring
  have hmono := intervalIntegral.integral_mono_on hab hlowint (hint.add hint') hpt
  rw [intervalIntegral.integral_add hint hint', hrefl, hlowval] at hmono
  -- conclude
  have hEδ : Real.exp (-(l ^ 2 * δ ^ 2 / 6) * (A + B)) = Real.exp (-c / 3) := by
    congr 1; rw [hc]; ring
  rw [hEδ, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith [hmono]

end MassartDKW.Tight

open MassartDKW.Tight


theorem solution (δ s : ℝ) (hδ : 0 < δ) (hδs : δ < s) (hs1 : s < 1 - δ) (g : ℝ → ℝ)
    (hg : ∀ u ∈ Set.Icc (s - δ) (s + δ), 0 < g u)
    (hlog : ConvexOn ℝ (Set.Icc (s - δ) (s + δ)) (fun u => Real.log (g u))) (l : ℝ) (hl : 0 < l) :
    g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s))) *
        Real.exp (-(l ^ 2 * δ ^ 2 / 6) *
          ((s * (s ^ 2 - δ ^ 2))⁻¹ + ((1 - s) * ((1 - s) ^ 2 - δ ^ 2))⁻¹)) ≤
      1 / (2 * δ) * ∫ u in (s - δ)..(s + δ), g u * Real.exp (-(l ^ 2) / (2 * u * (1 - u))) := by
  exact lemma_3_core δ s hδ hδs hs1 g hg hlog l hl
