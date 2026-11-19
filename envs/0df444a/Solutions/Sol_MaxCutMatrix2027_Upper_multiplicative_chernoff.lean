-- Prove2me | solution 1 for MaxCutMatrix2027.Upper.multiplicative_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:30:04.046824+00:00
-- url     : https://prove2.me/submissions/31f9ff91-888b-4d69-9818-200afca4f6d5

import Mathlib

open MeasureTheory ProbabilityTheory Set

/-- log(1+x) ≥ 2x/(2+x) for x ≥ 0 -/
lemma log_one_add_ge (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun y => Real.log (1 + y) - 2 * y / (2 + y)
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy
      have hy : (0:ℝ) ≤ y := hy
      apply ContinuousAt.continuousWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      apply DifferentiableAt.differentiableWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      have hd : HasDerivAt g (1 / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
        have a1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + y)) y := by
          have := ((hasDerivAt_id y).const_add 1).log (by simp; linarith)
          simpa [one_div] using this
        have a2 : HasDerivAt (fun y : ℝ => 2 * y / (2 + y))
            ((2 * 1 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
          have := ((hasDerivAt_id' y).const_mul 2).div ((hasDerivAt_id' y).const_add 2)
            (by linarith)
          exact this
        exact (a1.sub a2).congr_deriv (by ring)
      rw [hd.deriv]
      have : (1:ℝ) / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2 =
          y ^ 2 / ((1 + y) * (2 + y) ^ 2) := by
        field_simp; ring
      rw [this]; positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [g, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at this
  linarith

/-- (1-δ) log(1-δ) ≥ -δ + δ²/2 for δ ∈ [0,1) -/
lemma one_sub_log_ge (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    -δ + δ ^ 2 / 2 ≤ (1 - δ) * Real.log (1 - δ) := by
  let h : ℝ → ℝ := fun y => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2
  have hmono : MonotoneOn h (Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro y hy
      apply ContinuousAt.continuousWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      apply DifferentiableAt.differentiableWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      have hne : (1 - y) ≠ 0 := by linarith [hy.2]
      have hd : HasDerivAt h (-Real.log (1 - y) - y) y := by
        have a1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub 1
        have a2 := (a1.mul (a1.log hne))
        have a3 := (a2.add (hasDerivAt_id y)).sub ((hasDerivAt_pow 2 y).div_const 2)
        exact a3.congr_deriv (by field_simp; ring)
      rw [hd.deriv]
      have := Real.log_le_sub_one_of_pos (by linarith [hy.2] : (0:ℝ) < 1 - y)
      linarith
  have := hmono (mem_Ico.mpr ⟨le_rfl, by norm_num⟩) (mem_Ico.mpr ⟨h0, h1⟩) h0
  simp only [h, sub_zero, Real.log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith

lemma chord_exp' (c z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (c * z) ≤ 1 + z * (Real.exp c - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ c) (by linarith : 0 ≤ 1 - z) hz0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (c * z) = Real.exp (z * c) := by ring_nf
    _ ≤ (1 - z) + z * Real.exp c := h
    _ = _ := by ring

section Tails
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma mgf_le_chord (Z : Ω → ℝ) (hZm : Measurable Z) (hZ : ∀ᵐ ω ∂P, Z ω ∈ Icc (0:ℝ) 1) (c : ℝ) :
    mgf Z P c ≤ Real.exp ((Real.exp c - 1) * ∫ ω, Z ω ∂P) := by
  have hZi : Integrable Z P := by
    refine Integrable.mono' (integrable_const 1) hZm.aestronglyMeasurable ?_
    filter_upwards [hZ] with ω h; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2]
  have hEi : Integrable (fun ω => Real.exp (c * Z ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp |c|)) (by fun_prop) ?_
    filter_upwards [hZ] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have : |c * Z ω| ≤ |c| := by
      rw [abs_mul, abs_of_nonneg h.1]; exact mul_le_of_le_one_right (abs_nonneg c) h.2
    linarith [le_abs_self (c * Z ω)]
  rw [mgf]
  calc ∫ ω, Real.exp (c * Z ω) ∂P ≤ ∫ ω, (1 + Z ω * (Real.exp c - 1)) ∂P := by
        apply integral_mono_ae hEi ((integrable_const 1).add (hZi.mul_const _))
        filter_upwards [hZ] with ω h using chord_exp' c (Z ω) h.1 h.2
    _ = 1 + (∫ ω, Z ω ∂P) * (Real.exp c - 1) := by
        rw [integral_add (integrable_const 1) (hZi.mul_const _), integral_const, integral_mul_const]
        simp
    _ ≤ _ := by
        have := Real.add_one_le_exp ((Real.exp c - 1) * ∫ ω, Z ω ∂P); linarith

variable {m : ℕ} (X : Fin m → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
  (hX : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (0:ℝ) 1)
include hXm hind hX

lemma sum_mgf_le (c : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P c ≤ Real.exp ((Real.exp c - 1) * ∫ ω, ∑ i, X i ω ∂P) := by
  have hZi : ∀ i, Integrable (X i) P := by
    intro i
    refine Integrable.mono' (integrable_const 1) (hXm i).aestronglyMeasurable ?_
    filter_upwards [hX i] with ω h; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2]
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i, X i := by funext ω; simp
  have e := hind.mgf_sum hXm Finset.univ (t := c)
  rw [← hfun] at e
  rw [e, integral_finset_sum _ (fun i _ => hZi i), Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => mgf_le_chord P (X i) (hXm i) (hX i) c)

lemma sum_exp_int (c : ℝ) : Integrable (fun ω => Real.exp (c * ∑ i, X i ω)) P := by
  have hall : ∀ᵐ ω ∂P, ∀ i, X i ω ∈ Icc (0:ℝ) 1 := ae_all_iff.mpr hX
  refine Integrable.mono' (integrable_const (Real.exp (|c| * m))) (by fun_prop) ?_
  filter_upwards [hall] with ω h
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hs0 : 0 ≤ ∑ i, X i ω := Finset.sum_nonneg (fun i _ => (h i).1)
  have hs1 : ∑ i, X i ω ≤ m := by
    calc ∑ i, X i ω ≤ ∑ _i : Fin m, (1:ℝ) := Finset.sum_le_sum (fun i _ => (h i).2)
      _ = m := by simp
  calc c * ∑ i, X i ω ≤ |c| * ∑ i, X i ω := mul_le_mul_of_nonneg_right (le_abs_self c) hs0
    _ ≤ |c| * m := mul_le_mul_of_nonneg_left hs1 (abs_nonneg c)

lemma lower_raw (t : ℝ) (ht : 0 < t) (htM : t ≤ ∫ ω, ∑ i, X i ω ∂P) :
    P.real {ω | ∑ i, X i ω ≤ t} ≤
      Real.exp (t * Real.log ((∫ ω, ∑ i, X i ω ∂P) / t) + t - ∫ ω, ∑ i, X i ω ∂P) := by
  set M := ∫ ω, ∑ i, X i ω ∂P
  have hM0 : 0 < M := lt_of_lt_of_le ht htM
  set c := Real.log (M / t) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hec : Real.exp (-c) = t / M := by
    rw [hc, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i, X i ω) t
    (neg_nonpos.mpr hc0) (sum_exp_int P X hXm hind hX (-c))
  refine h1.trans ?_
  have h2 := sum_mgf_le P X hXm hind hX (-c)
  rw [hec] at h2
  calc Real.exp (- -c * t) * mgf (fun ω => ∑ i, X i ω) P (-c)
      ≤ Real.exp (- -c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma upper_raw (t : ℝ) (hM : 0 < ∫ ω, ∑ i, X i ω ∂P) (htM : ∫ ω, ∑ i, X i ω ∂P ≤ t) :
    P.real {ω | t ≤ ∑ i, X i ω} ≤
      Real.exp (-(t * Real.log (t / ∫ ω, ∑ i, X i ω ∂P)) + t - ∫ ω, ∑ i, X i ω ∂P) := by
  set M := ∫ ω, ∑ i, X i ω ∂P
  have ht : 0 < t := lt_of_lt_of_le hM htM
  set c := Real.log (t / M) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hM]; linarith)
  have hec : Real.exp c = t / M := by rw [hc, Real.exp_log (by positivity)]
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i, X i ω) t hc0
    (sum_exp_int P X hXm hind hX c)
  refine h1.trans ?_
  have h2 := sum_mgf_le P X hXm hind hX c
  rw [hec] at h2
  calc Real.exp (-c * t) * mgf (fun ω => ∑ i, X i ω) P c
      ≤ Real.exp (-c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma lower_zero :
    P.real {ω | ∑ i, X i ω ≤ 0} ≤ Real.exp (-(∫ ω, ∑ i, X i ω ∂P) / 3) := by
  set c := Real.log (3 / 2) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by norm_num)
  have hec : Real.exp (-c) = 2 / 3 := by
    rw [hc, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i, X i ω) 0
    (neg_nonpos.mpr hc0) (sum_exp_int P X hXm hind hX (-c))
  refine h1.trans ?_
  have h2 := sum_mgf_le P X hXm hind hX (-c)
  rw [hec] at h2
  rw [mul_zero, Real.exp_zero, one_mul]
  refine h2.trans (le_of_eq ?_)
  congr 1; ring

end Tails

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : 0 < ∫ ω, ∑ i, X i ω ∂μ) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | (1 + δ) * (∫ z, ∑ i, X i z ∂μ) ≤ ∑ i, X i ω} ≤
      Real.exp (-(δ ^ 2 * (∫ z, ∑ i, X i z ∂μ)) / (2 + δ)) := by
  set M := ∫ z, ∑ i, X i z ∂μ with hM
  refine (upper_raw μ X hX hind hb ((1 + δ) * M) hmean (by nlinarith)).trans ?_
  apply Real.exp_le_exp.mpr
  have hlog : Real.log ((1 + δ) * M / M) = Real.log (1 + δ) := by
    rw [show (1 + δ) * M / M = 1 + δ by field_simp]
  rw [hlog]
  have hl := log_one_add_ge δ hδ.le
  have h2 : 0 < 2 + δ := by linarith
  rw [div_le_iff₀ h2] at hl
  rw [neg_div, le_neg, div_le_iff₀ h2]
  nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ (1 + δ) * M)]
