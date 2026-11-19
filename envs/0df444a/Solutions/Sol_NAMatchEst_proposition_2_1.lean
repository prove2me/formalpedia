-- Prove2me | solution 1 for NAMatchEst.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:45:10.063079+00:00
-- url     : https://prove2.me/submissions/b7dfaccb-1b40-42dd-8163-dc54048b0046

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

section OneSided
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ) (hint : ∀ c, Integrable (fun ω => Real.exp (c * Y ω)) P)
include hint

lemma upper_os (H : ℝ) (hmgf : ∀ c, 0 ≤ c → mgf Y P c ≤ Real.exp ((Real.exp c - 1) * H))
    (t : ℝ) (hH : 0 < H) (htH : H ≤ t) :
    P.real {ω | t ≤ Y ω} ≤ Real.exp (-(t * Real.log (t / H)) + t - H) := by
  have ht : 0 < t := lt_of_lt_of_le hH htH
  set c := Real.log (t / H) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hH]; linarith)
  have hec : Real.exp c = t / H := by rw [hc, Real.exp_log (by positivity)]
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := Y) t hc0 (hint c)
  refine h1.trans ?_
  have h2 := hmgf c hc0
  rw [hec] at h2
  calc Real.exp (-c * t) * mgf Y P c
      ≤ Real.exp (-c * t) * Real.exp ((t / H - 1) * H) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma lower_os (L : ℝ) (hmgf : ∀ c, 0 ≤ c → mgf Y P (-c) ≤ Real.exp ((Real.exp (-c) - 1) * L))
    (t : ℝ) (ht : 0 < t) (htL : t ≤ L) :
    P.real {ω | Y ω ≤ t} ≤ Real.exp (t * Real.log (L / t) + t - L) := by
  have hL0 : 0 < L := lt_of_lt_of_le ht htL
  set c := Real.log (L / t) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hec : Real.exp (-c) = t / L := by
    rw [hc, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := Y) t (neg_nonpos.mpr hc0) (hint (-c))
  refine h1.trans ?_
  have h2 := hmgf c hc0
  rw [hec] at h2
  calc Real.exp (- -c * t) * mgf Y P (-c)
      ≤ Real.exp (- -c * t) * Real.exp ((t / L - 1) * L) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma lower_zero_os (L : ℝ) (hmgf : ∀ c, 0 ≤ c → mgf Y P (-c) ≤ Real.exp ((Real.exp (-c) - 1) * L)) :
    P.real {ω | Y ω ≤ 0} ≤ Real.exp (-L / 3) := by
  set c := Real.log (3 / 2) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by norm_num)
  have hec : Real.exp (-c) = 2 / 3 := by
    rw [hc, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := Y) 0 (neg_nonpos.mpr hc0) (hint (-c))
  refine h1.trans ?_
  have h2 := hmgf c hc0
  rw [hec] at h2
  rw [mul_zero, Real.exp_zero, one_mul]
  refine h2.trans (le_of_eq ?_)
  congr 1; ring

end OneSided

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (X : Fin m → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hrange : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (lamL lamH : ℝ)
    (hL : lamL ≤ ∫ ω, ∑ i, X i ω ∂P) (hH : ∫ ω, ∑ i, X i ω ∂P ≤ lamH) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (1 + ε) * lamH ≤ ∑ i, X i ω} ≤ Real.exp (-(ε ^ 2 * lamH) / (3 + ε)) ∧
      P.real {ω | ∑ i, X i ω ≤ (1 - ε) * lamL} ≤ Real.exp (-(ε ^ 2 * lamL) / (2 + ε)) := by
  have hX : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (0:ℝ) 1 := fun i => Filter.Eventually.of_forall (hrange i)
  set M := ∫ ω, ∑ i, X i ω ∂P with hM
  have hM0 : 0 ≤ M := integral_nonneg (fun ω => Finset.sum_nonneg (fun i _ => (hrange i ω).1))
  have hmgf := sum_mgf_le P X hmeas hindep hX
  have hint := sum_exp_int P X hmeas hindep hX
  constructor
  · have hHmgf : ∀ c, 0 ≤ c → mgf (fun ω => ∑ i, X i ω) P c ≤ Real.exp ((Real.exp c - 1) * lamH) := by
      intro c hc
      refine (hmgf c).trans (Real.exp_le_exp.mpr ?_)
      have : 0 ≤ Real.exp c - 1 := by linarith [Real.one_le_exp hc]
      exact mul_le_mul_of_nonneg_left hH this
    rcases (hM0.trans hH).eq_or_lt with hz | hHpos
    · rw [← hz]; simp only [mul_zero, neg_zero, zero_div, Real.exp_zero]; exact measureReal_le_one
    refine (upper_os P (fun ω => ∑ i, X i ω) hint lamH hHmgf ((1 + ε) * lamH) hHpos
      (by nlinarith)).trans ?_
    apply Real.exp_le_exp.mpr
    have hlog : Real.log ((1 + ε) * lamH / lamH) = Real.log (1 + ε) := by
      rw [show (1 + ε) * lamH / lamH = 1 + ε by field_simp]
    rw [hlog]
    have hl := log_one_add_ge ε hε.le
    have h2 : 0 < 2 + ε := by linarith
    rw [div_le_iff₀ h2] at hl
    have hl' := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ (1 + ε) * lamH)
    have key0 : ε ^ 2 * lamH / (2 + ε) ≤ (1 + ε) * lamH * Real.log (1 + ε) - ε * lamH := by
      rw [div_le_iff₀ h2]; nlinarith
    have : ε ^ 2 * lamH / (3 + ε) ≤ ε ^ 2 * lamH / (2 + ε) :=
      div_le_div_of_nonneg_left (by positivity) h2 (by linarith)
    rw [neg_div]; linarith
  · have hLmgf : ∀ c, 0 ≤ c → mgf (fun ω => ∑ i, X i ω) P (-c) ≤
        Real.exp ((Real.exp (-c) - 1) * lamL) := by
      intro c hc
      refine (hmgf (-c)).trans (Real.exp_le_exp.mpr ?_)
      have : Real.exp (-c) - 1 ≤ 0 := by
        have := Real.exp_le_one_iff.mpr (by linarith : -c ≤ 0); linarith
      exact mul_le_mul_of_nonpos_left hL this
    rcases le_or_gt lamL 0 with hLn | hLpos
    · refine measureReal_le_one.trans ?_
      apply Real.one_le_exp
      have : ε ^ 2 * lamL ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hLn
      rw [neg_div]; apply neg_nonneg.mpr; exact div_nonpos_of_nonpos_of_nonneg this (by linarith)
    rcases lt_trichotomy ε 1 with hlt | heq | hgt
    · refine (lower_os P (fun ω => ∑ i, X i ω) hint lamL hLmgf ((1 - ε) * lamL) (by nlinarith)
        (by nlinarith)).trans ?_
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (lamL / ((1 - ε) * lamL)) = -Real.log (1 - ε) := by
        rw [show lamL / ((1 - ε) * lamL) = (1 - ε)⁻¹ by field_simp, Real.log_inv]
      rw [hlog]
      have := one_sub_log_ge ε hε.le hlt
      have h3 : ε ^ 2 * lamL / (2 + ε) ≤ ε ^ 2 * lamL / 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      rw [neg_div]; nlinarith
    · subst heq
      have := lower_zero_os P (fun ω => ∑ i, X i ω) hint lamL hLmgf
      simp only [sub_self, zero_mul]
      refine this.trans (le_of_eq ?_)
      congr 1; ring
    · have hempty : {ω | ∑ i, X i ω ≤ (1 - ε) * lamL} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        have : 0 ≤ ∑ i, X i ω := Finset.sum_nonneg (fun i _ => (hrange i ω).1)
        nlinarith
      rw [hempty, measureReal_empty]; positivity
