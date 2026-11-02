-- Prove2me | solution 1 for LiqProvision.Oligopoly.proposition_D_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:12:29.651713+00:00
-- url     : https://prove2.me/submissions/f11a33f1-2484-4bf5-ad87-0943bd77b05d

import Mathlib
import Theorems.Thm_LiqProvision_Oligopoly_proposition_D_1
import Theorems.Thm_LiqProvision_Oligopoly_proposition_D_2

open Set MeasureTheory Filter Topology

namespace LiqD3Aux

theorem logconcave_continuous {F : ℝ → ℝ} (hpos : ∀ x, 0 < F x)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (F x))) : Continuous F := by
  have h1 : Continuous (fun x => Real.log (F x)) := by
    rw [← continuousOn_univ]; exact hc.continuousOn isOpen_univ
  have : F = fun x => Real.exp (Real.log (F x)) := funext fun x => (Real.exp_log (hpos x)).symm
  rw [this]; exact h1.rexp

/-- a right derivative of a continuous function is measurable -/
theorem rderiv_measurable {f f' : ℝ → ℝ} (hfc : Continuous f)
    (hf' : ∀ x, HasDerivWithinAt f (f' x) (Ici x) x) : Measurable f' := by
  set q : ℕ → ℝ → ℝ := fun n x => (f (x + 1 / ((n:ℝ) + 1)) - f x) * ((n:ℝ) + 1) with hq
  apply measurable_of_tendsto_metrizable (f := q)
  · intro n
    apply Continuous.measurable
    simp only [hq]; fun_prop
  · rw [tendsto_pi_nhds]
    intro x
    have ht := hasDerivWithinAt_iff_tendsto_slope.1 (hf' x)
    have hu : Tendsto (fun n : ℕ => x + 1 / ((n:ℝ) + 1)) atTop (𝓝[Ici x \ {x}] x) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds (x := x)).add this
      · refine Eventually.of_forall fun n => ?_
        have : 0 < 1 / ((n:ℝ) + 1) := by positivity
        simp only [mem_diff, mem_Ici, mem_singleton_iff]
        constructor <;> [linarith; (intro h; linarith)]
    refine (ht.comp hu).congr (fun n => ?_)
    simp only [Function.comp, hq, slope_def_field]
    have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- integrability of a unimodal right derivative of a positive function -/
theorem rderiv_integrable {f f' : ℝ → ℝ} (hfc : Continuous f) (hpos : ∀ x, 0 < f x)
    (hf' : ∀ x, HasDerivWithinAt f (f' x) (Ici x) x) (xs : ℝ)
    (h1 : ∀ x < xs, 0 ≤ f' x) (h2 : ∀ x, xs ≤ x → f' x ≤ 0) : Integrable f' := by
  have hd : ∀ x, HasDerivWithinAt f (f' x) (Ioi x) x :=
    fun x => hasDerivWithinAt_Ioi_iff_Ici.2 (hf' x)
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ xs := by
    rw [ae_iff]; simp
  have hleft : IntegrableOn f' (Iic xs) := by
    have hI : ∀ n : ℕ, IntegrableOn f' (Ioc (xs - n) xs) := fun n =>
      intervalIntegral.integrableOn_deriv_right_of_nonneg hfc.continuousOn
        (fun x _ => hd x) (fun x hx => h1 x hx.2)
    refine integrableOn_Iic_of_intervalIntegral_norm_bounded (l := atTop)
      (a := fun n : ℕ => xs - n) (f xs) xs hI ?_ ?_
    · rw [tendsto_atTop_atBot]
      intro b
      refine ⟨⌈xs - b⌉₊, fun n hn => ?_⟩
      have := (Nat.le_ceil (xs - b)).trans (Nat.cast_le.2 hn)
      linarith
    · refine Eventually.of_forall fun n => ?_
      have hn : xs - n ≤ xs := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have hii : IntervalIntegrable f' volume (xs - n) xs :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hn).2 (hI n)
      have heq : ∫ x in (xs - n)..xs, ‖f' x‖ = ∫ x in (xs - n)..xs, f' x := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hae] with x hx hmem
        rw [uIoc_of_le hn] at hmem
        rw [Real.norm_eq_abs, abs_of_nonneg (h1 x (lt_of_le_of_ne hmem.2 hx))]
      rw [heq, intervalIntegral.integral_eq_sub_of_hasDeriv_right hfc.continuousOn
        (fun x _ => hd x) hii]
      linarith [hpos (xs - n)]
  have hright : IntegrableOn f' (Ioi xs) := by
    have hI : ∀ n : ℕ, IntegrableOn f' (Ioc xs (xs + n)) := by
      intro n
      have := intervalIntegral.integrableOn_deriv_right_of_nonneg (g := fun x => -f x)
        (g' := fun x => -f' x) (a := xs) (b := xs + n) hfc.neg.continuousOn
        (fun x _ => (hd x).neg) (fun x hx => by simp; exact h2 x hx.1.le)
      simpa using this.neg
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop)
      (b := fun n : ℕ => xs + n) (f xs) xs hI ?_ ?_
    · rw [tendsto_atTop_atTop]
      intro b
      refine ⟨⌈b - xs⌉₊, fun n hn => ?_⟩
      have := (Nat.le_ceil (b - xs)).trans (Nat.cast_le.2 hn)
      linarith
    refine Eventually.of_forall fun n => ?_
    have hn : xs ≤ xs + n := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hii : IntervalIntegrable f' volume xs (xs + n) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hn).2 (hI n)
    have heq : ∫ x in xs..(xs + n), ‖f' x‖ = ∫ x in xs..(xs + n), -f' x := by
      apply intervalIntegral.integral_congr_ae
      refine Eventually.of_forall fun x hmem => ?_
      rw [uIoc_of_le hn] at hmem
      rw [Real.norm_eq_abs, abs_of_nonpos (h2 x hmem.1.le)]
    rw [heq, intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDeriv_right
      hfc.continuousOn (fun x _ => hd x) hii]
    linarith [hpos (xs + n)]
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := xs)]
  exact hleft.union hright

theorem integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp (-a * |y|)) := by
  have hI : IntegrableOn (fun y : ℝ => Real.exp (-a * y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact exp_neg_integrableOn_Ioi 0 ha
  have hI' := (integrable_indicator_iff measurableSet_Ici).2 hI
  refine Integrable.mono' (hI'.add hI'.comp_neg)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, indicator_of_mem (show y ∈ Ici 0 from hy)]
    have : 0 ≤ (Ici (0:ℝ)).indicator (fun y => Real.exp (-a * y)) (-y) :=
      indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    linarith
  · rw [abs_of_nonpos hy, indicator_of_mem (show -y ∈ Ici 0 by simp; linarith)]
    have : 0 ≤ (Ici (0:ℝ)).indicator (fun y => Real.exp (-a * y)) y :=
      indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    have e : -a * -y = -a * -y := rfl
    linarith

/-- an integrable function cannot be bounded below by a positive constant on a half-line -/
theorem not_bdd_Ici {f : ℝ → ℝ} (hint : Integrable f) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, 0 ≤ x → c ≤ f x) : False := by
  have hI : IntegrableOn (fun _ => c) (Ici (0:ℝ)) := by
    refine Integrable.mono' hint.integrableOn aestronglyMeasurable_const ?_
    refine (ae_restrict_mem measurableSet_Ici).mono fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos hc]; exact h x hx
  rw [integrableOn_const_iff] at hI
  rcases hI with h1 | h1
  · simp at h1; linarith
  · simp at h1

theorem not_bdd_Iic {f : ℝ → ℝ} (hint : Integrable f) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≤ 0 → c ≤ f x) : False := by
  have hI : IntegrableOn (fun _ => c) (Iic (0:ℝ)) := by
    refine Integrable.mono' hint.integrableOn aestronglyMeasurable_const ?_
    refine (ae_restrict_mem measurableSet_Iic).mono fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos hc]; exact h x hx
  rw [integrableOn_const_iff] at hI
  rcases hI with h1 | h1
  · simp at h1; linarith
  · simp at h1

/-- the right derivative of a concave function is antitone -/
theorem rderiv_antitone {φ ψ : ℝ → ℝ} (hlc : ConcaveOn ℝ univ φ)
    (hψd : ∀ x, HasDerivWithinAt φ (ψ x) (Ioi x) x) : Antitone ψ := by
  have hψ_le : ∀ x y, x < y → ψ y ≤ (φ y - φ x) / (y - x) := by
    intro x y hxy
    have ht := (hasDerivWithinAt_iff_tendsto_slope.1 (hψd y))
    have hset : Ioi y \ {y} = Ioi y := by ext z; simp
    rw [hset] at ht
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [slope_def_field]
    exact hlc.slope_anti_adjacent (mem_univ x) (mem_univ z) hxy hz
  have hψ_ge : ∀ x y, x < y → (φ y - φ x) / (y - x) ≤ ψ x := by
    intro x y hxy
    have := hlc.slope_le_rightDeriv (mem_univ x) (mem_univ y) hxy (hψd x).differentiableWithinAt
    rw [slope_def_field] at this
    have e : derivWithin φ (Ioi x) x = ψ x :=
      (hψd x).derivWithin (uniqueDiffWithinAt_Ioi x)
    rw [e] at this; exact this
  intro x y hxy
  rcases hxy.lt_or_eq with h | rfl
  · exact (hψ_le x y h).trans (hψ_ge x y h)
  · exact le_rfl

/-- a positive integrable function cannot have constant logarithmic right derivative -/
theorem not_const_rderiv {f ψ : ℝ → ℝ} (hpos : ∀ x, 0 < f x) (hint : Integrable f)
    (hfc : Continuous f) (hψd : ∀ x, HasDerivWithinAt (fun x => Real.log (f x)) (ψ x) (Ici x) x)
    (b : ℝ) (hb : ∀ x, ψ x = b) : False := by
  set φ : ℝ → ℝ := fun x => Real.log (f x) with hφ
  have hφc : Continuous φ := hfc.log (fun x => (hpos x).ne')
  have hz : ∀ x, HasDerivWithinAt (fun x => φ x - b * x) 0 (Ici x) x := by
    intro x
    have h := (hψd x).sub ((hasDerivAt_id x).const_mul b).hasDerivWithinAt
    rw [hb x, mul_one, sub_self] at h; exact h
  have hcont : Continuous (fun x => φ x - b * x) := hφc.sub (continuous_const.mul continuous_id)
  have hconst : ∀ x, φ x - b * x = φ 0 := by
    intro x
    rcases le_total 0 x with hx | hx
    · have := constant_of_has_deriv_right_zero hcont.continuousOn (fun y _ => hz y) x ⟨hx, le_rfl⟩
      simpa using this
    · have := constant_of_has_deriv_right_zero (a := x) (b := 0) hcont.continuousOn
        (fun y _ => hz y) 0 ⟨hx, le_rfl⟩
      simp at this; linarith
  have hf : ∀ x, f x = f 0 * Real.exp (b * x) := by
    intro x
    have h1 := hconst x
    have e : ∀ z, f z = Real.exp (φ z) := fun z => (Real.exp_log (hpos z)).symm
    rw [e x, e 0, ← Real.exp_add]; congr 1; linarith
  rcases le_total 0 b with hb0 | hb0
  · apply not_bdd_Ici hint (hpos 0)
    intro x hx
    rw [hf x]
    have : 1 ≤ Real.exp (b * x) := Real.one_le_exp (mul_nonneg hb0 hx)
    nlinarith [hpos 0]
  · apply not_bdd_Iic hint (hpos 0)
    intro x hx
    rw [hf x]
    have : 1 ≤ Real.exp (b * x) := Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos hb0 hx)
    nlinarith [hpos 0]

end LiqD3Aux

open LiqD3Aux in
theorem solution (fU fV : ℝ → ℝ)
    (hUpos : ∀ x, 0 < fU x) (hUint : MeasureTheory.Integrable fU) (hUmass : ∫ x, fU x = 1)
    (hUlc : ConcaveOn ℝ Set.univ (fun x => Real.log (fU x)))
    (hVpos : ∀ x, 0 < fV x) (hVint : MeasureTheory.Integrable fV) (hVmass : ∫ x, fV x = 1)
    (hVlc : ConcaveOn ℝ Set.univ (fun x => Real.log (fV x))) :
    ContDiff ℝ 1 (fun w => (∫ v, (w - v) * fU (w - v) * fV v) / ∫ v, fU (w - v) * fV v) ∧
      ∀ w, 0 < deriv (fun w =>
        (∫ v, (w - v) * fU (w - v) * fV v) / ∫ v, fU (w - v) * fV v) w := by
  obtain ⟨-, ⟨CV, εV, hCV, hεV, hVtail⟩, ⟨fV', hfV', xs, hxs1, hxs2⟩⟩ :=
    LiqProvision.Oligopoly.proposition_D_1 fV hVpos hVint hVmass hVlc
  obtain ⟨-, ⟨CU, εU, hCU, hεU, hUtail⟩, -⟩ :=
    LiqProvision.Oligopoly.proposition_D_1 fU hUpos hUint hUmass hUlc
  obtain ⟨⟨hcpos, -, -, -, hcC1, -, hcderiv⟩, ⟨-, hc2C1, -, hc2deriv⟩⟩ :=
    LiqProvision.Oligopoly.proposition_D_2 fV fU hVpos hVint hVmass hVlc hUpos hUint hUmass
      hUlc fV' hfV'
  have hVc := logconcave_continuous hVpos hVlc
  have hUc := logconcave_continuous hUpos hUlc
  set c : ℝ → ℝ := fun x => ∫ y, fV (x - y) * fU y with hc
  set c₂ : ℝ → ℝ := fun x => ∫ y, fV (x - y) * (y * fU y) with hc₂
  have hD : (fun w => ∫ v, fU (w - v) * fV v) = c := by
    funext w
    have := integral_sub_left_eq_self (fun v => fU (w - v) * fV v) volume w
    rw [← this]; simp only [hc, sub_sub_cancel]; congr 1; funext y; ring
  have hN : (fun w => ∫ v, (w - v) * fU (w - v) * fV v) = c₂ := by
    funext w
    have := integral_sub_left_eq_self (fun v => (w - v) * fU (w - v) * fV v) volume w
    rw [← this]; simp only [hc₂, sub_sub_cancel]; congr 1; funext y; ring
  have hg : (fun w => (∫ v, (w - v) * fU (w - v) * fV v) / ∫ v, fU (w - v) * fV v) =
      fun w => c₂ w / c w := by
    funext w
    exact congrArg₂ (· / ·) (congrFun hN w) (congrFun hD w)
  rw [hg]
  refine ⟨hc2C1.div hcC1 (fun w => (hcpos w).ne'), fun w => ?_⟩
  -- derivatives
  have hcd : HasDerivAt c (∫ y, fV' (w - y) * fU y) w := by
    rw [← hcderiv w]; exact (hcC1.differentiable (by norm_num) w).hasDerivAt
  have hc2d : HasDerivAt c₂ (∫ y, fV' (w - y) * (y * fU y)) w := by
    rw [← hc2deriv w]; exact (hc2C1.differentiable (by norm_num) w).hasDerivAt
  have hdiv := hc2d.div hcd (hcpos w).ne'
  have e : (fun w => c₂ w / c w) = c₂ / c := rfl
  rw [e, hdiv.deriv]
  apply div_pos _ (pow_pos (hcpos w) 2)
  -- the numerator
  have hfVm : Measurable fV' := rderiv_measurable hVc hfV'
  have hfVi : Integrable fV' := rderiv_integrable hVc hVpos hfV' xs hxs1 hxs2
  have hVB : ∀ x, |fV x| ≤ CV := by
    intro x
    rw [abs_of_pos (hVpos x)]
    calc fV x ≤ CV * Real.exp (-εV * |x|) := hVtail x
      _ ≤ CV * 1 := by
        apply mul_le_mul_of_nonneg_left _ hCV.le
        rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg x]
      _ = CV := mul_one _
  have hUB : ∀ x, |fU x| ≤ CU := by
    intro x
    rw [abs_of_pos (hUpos x)]
    calc fU x ≤ CU * Real.exp (-εU * |x|) := hUtail x
      _ ≤ CU * 1 := by
        apply mul_le_mul_of_nonneg_left _ hCU.le
        rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg x]
      _ = CU := mul_one _
  have hyUB : ∀ y, |y * fU y| ≤ CU / εU := by
    intro y
    rw [abs_mul, abs_of_pos (hUpos y), le_div_iff₀ hεU]
    have h1 := hUtail y
    have h2 : εU * |y| ≤ Real.exp (εU * |y|) := by
      have := Real.add_one_le_exp (εU * |y|); linarith
    have h3 : Real.exp (-εU * |y|) * Real.exp (εU * |y|) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : |y| * fU y * εU ≤ |y| * (CU * Real.exp (-εU * |y|)) * εU :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg y)) hεU.le
    have h5 : |y| * (CU * Real.exp (-εU * |y|)) * εU =
        CU * Real.exp (-εU * |y|) * (εU * |y|) := by ring
    have h6 : CU * Real.exp (-εU * |y|) * (εU * |y|) ≤
        CU * Real.exp (-εU * |y|) * Real.exp (εU * |y|) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hyUc : Continuous (fun y => y * fU y) := continuous_id.mul hUc
  have hyUi : Integrable (fun y => y * fU y) := by
    have hexp := (integrable_exp_neg_abs (a := εU / 2) (by positivity)).const_mul
      (CU * (2 / εU))
    refine Integrable.mono' hexp hyUc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hUpos y)]
    have h1 := hUtail y
    have h2 : εU / 2 * |y| ≤ Real.exp (εU / 2 * |y|) := by
      have := Real.add_one_le_exp (εU / 2 * |y|); linarith
    have h3 : Real.exp (-εU * |y|) = Real.exp (-(εU / 2) * |y|) * Real.exp (-(εU / 2) * |y|) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (-(εU / 2) * |y|) * Real.exp (εU / 2 * |y|) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : |y| ≤ 2 / εU * Real.exp (εU / 2 * |y|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hεU]; linarith
    have hE := Real.exp_pos (-(εU / 2) * |y|)
    calc |y| * fU y ≤ |y| * (CU * Real.exp (-εU * |y|)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg y)
      _ = CU * Real.exp (-(εU / 2) * |y|) * (|y| * Real.exp (-(εU / 2) * |y|)) := by
          rw [h3]; ring
      _ ≤ CU * Real.exp (-(εU / 2) * |y|) *
            (2 / εU * Real.exp (εU / 2 * |y|) * Real.exp (-(εU / 2) * |y|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h5 hE.le
      _ = CU * (2 / εU) * Real.exp (-(εU / 2) * |y|) := by
          rw [mul_assoc (2 / εU), mul_comm (Real.exp (εU / 2 * |y|)), h4]; ring
  set A₁ : ℝ → ℝ := fun u => fV' (w - u) * (u * fU u) with hA₁
  set B₁ : ℝ → ℝ := fun u => fV (w - u) * fU u with hB₁
  set A₂ : ℝ → ℝ := fun u => fV (w - u) * (u * fU u) with hA₂
  set B₂ : ℝ → ℝ := fun u => fV' (w - u) * fU u with hB₂
  have iA₁ : Integrable A₁ := by
    have := (hfVi.comp_sub_left w).bdd_mul (c := CU / εU) hyUc.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hyUB y)
    simpa [hA₁, mul_comm] using this
  have iB₁ : Integrable B₁ :=
    hUint.bdd_mul (c := CV) (hVc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hVB _)
  have iA₂ : Integrable A₂ :=
    hyUi.bdd_mul (c := CV) (hVc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hVB _)
  have iB₂ : Integrable B₂ := by
    have := (hfVi.comp_sub_left w).bdd_mul (c := CU) hUc.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hUB y)
    simpa [hB₂, mul_comm] using this
  set G : ℝ × ℝ → ℝ := fun p => A₁ p.1 * B₁ p.2 - A₂ p.1 * B₂ p.2 with hG
  have hI1 : Integrable (fun p : ℝ × ℝ => A₁ p.1 * B₁ p.2) (volume.prod volume) :=
    iA₁.mul_prod iB₁
  have hI2 : Integrable (fun p : ℝ × ℝ => A₂ p.1 * B₂ p.2) (volume.prod volume) :=
    iA₂.mul_prod iB₂
  have hGI : Integrable G (volume.prod volume) := hI1.sub hI2
  have hnum : (∫ y, fV' (w - y) * (y * fU y)) * c w - c₂ w * (∫ y, fV' (w - y) * fU y) =
      ∫ p, G p ∂(volume.prod volume) := by
    rw [integral_sub hI1 hI2, integral_prod_mul A₁ B₁, integral_prod_mul A₂ B₂]
  rw [hnum]
  have hsw : ∫ p, G p.swap ∂(volume.prod volume) = ∫ p, G p ∂(volume.prod volume) :=
    integral_prod_swap G
  -- log-derivative of fV
  set ψ : ℝ → ℝ := fun x => fV' x / fV x with hψ
  have hψd : ∀ x, HasDerivWithinAt (fun x => Real.log (fV x)) (ψ x) (Ici x) x :=
    fun x => (hfV' x).log (hVpos x).ne'
  have hψanti : Antitone ψ :=
    rderiv_antitone hVlc (fun x => hasDerivWithinAt_Ioi_iff_Ici.2 (hψd x))
  have hfV'eq : ∀ x, fV' x = fV x * ψ x := by
    intro x; simp only [hψ]; rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (hVpos x).ne', mul_one]
  set H : ℝ × ℝ → ℝ := fun p => G p + G p.swap with hH
  have hHform : ∀ u₁ u₂ : ℝ, H (u₁, u₂) = (u₁ - u₂) * fU u₁ * fU u₂ * fV (w - u₁) *
      fV (w - u₂) * (ψ (w - u₁) - ψ (w - u₂)) := by
    intro u₁ u₂
    simp only [hH, hG, hA₁, hB₁, hA₂, hB₂, Prod.swap, hfV'eq]
    ring
  have hHnn : ∀ p, 0 ≤ H p := by
    rintro ⟨u₁, u₂⟩
    rw [hHform]
    have hpos4 : 0 < fU u₁ * fU u₂ * fV (w - u₁) * fV (w - u₂) := by
      have := hUpos u₁; have := hUpos u₂; have := hVpos (w - u₁); have := hVpos (w - u₂)
      positivity
    rcases le_total u₂ u₁ with h | h
    · have hψ' : ψ (w - u₂) ≤ ψ (w - u₁) := hψanti (by linarith)
      have : 0 ≤ (u₁ - u₂) * (ψ (w - u₁) - ψ (w - u₂)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have hψ' : ψ (w - u₁) ≤ ψ (w - u₂) := hψanti (by linarith)
      have : 0 ≤ (u₁ - u₂) * (ψ (w - u₁) - ψ (w - u₂)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith
  have hGs : Integrable (fun p : ℝ × ℝ => G p.swap) (volume.prod volume) := hGI.swap
  have hHI : Integrable H (volume.prod volume) := hGI.add hGs
  -- ψ is not constant
  obtain ⟨p, q, hpq, hψpq⟩ : ∃ p q, p < q ∧ ψ q < ψ p := by
    by_contra hcon
    push Not at hcon
    apply not_const_rderiv hVpos hVint hVc hψd (ψ 0)
    intro x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · exact le_antisymm (hcon x 0 hx) (hψanti hx.le)
    · rfl
    · exact le_antisymm (hψanti hx.le) (hcon 0 x hx)
  have hHpos : 0 < ∫ p, H p ∂(volume.prod volume) := by
    rw [integral_pos_iff_support_of_nonneg hHnn hHI]
    have hsub : Ioi (w - p) ×ˢ Iio (w - q) ⊆ Function.support H := by
      rintro ⟨u₁, u₂⟩ ⟨h1, h2⟩
      simp only [mem_Ioi, mem_Iio] at h1 h2
      rw [Function.mem_support, hHform]
      have hψ1 : ψ p ≤ ψ (w - u₁) := hψanti (by linarith)
      have hψ2 : ψ (w - u₂) ≤ ψ q := hψanti (by linarith)
      have := hUpos u₁; have := hUpos u₂; have := hVpos (w - u₁); have := hVpos (w - u₂)
      have hd : 0 < u₁ - u₂ := by linarith
      have hdψ : 0 < ψ (w - u₁) - ψ (w - u₂) := by linarith
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Measure.prod_prod, Real.volume_Ioi, Real.volume_Iio]
    simp
  have h2 : ∫ p, H p ∂(volume.prod volume) = 2 * ∫ p, G p ∂(volume.prod volume) := by
    simp only [hH]
    rw [integral_add hGI hGs, hsw]; ring
  linarith
