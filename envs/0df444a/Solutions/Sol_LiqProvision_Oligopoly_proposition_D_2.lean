-- Prove2me | solution 1 for LiqProvision.Oligopoly.proposition_D_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:08:34.989143+00:00
-- url     : https://prove2.me/submissions/157c4f3d-c69d-427f-bdc0-61311fbe5e48

import Mathlib
import Theorems.Thm_LiqProvision_Oligopoly_proposition_D_1

open Set MeasureTheory Filter Topology

namespace LiqD2Aux

/-- four-point inequality for concave functions -/
theorem four_point {φ : ℝ → ℝ} (hc : ConcaveOn ℝ univ φ) {u x d : ℝ} (hux : u ≤ x)
    (hd : 0 ≤ d) : φ (x + d) + φ u ≤ φ x + φ (u + d) := by
  rcases hux.lt_or_eq with hux | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hL : 0 < x + d - u := by linarith
      set w := d / (x + d - u) with hw
      have hw0 : 0 < w := div_pos hd hL
      have hw1 : w < 1 := by rw [hw, div_lt_one hL]; linarith
      have h1 := hc.2 (mem_univ u) (mem_univ (x + d)) hw0.le (by linarith : 0 ≤ 1 - w)
        (by ring)
      have h2 := hc.2 (mem_univ u) (mem_univ (x + d)) (by linarith : 0 ≤ 1 - w) hw0.le
        (by ring)
      simp only [smul_eq_mul] at h1 h2
      have e1 : w * u + (1 - w) * (x + d) = x := by rw [hw]; field_simp; ring
      have e2 : (1 - w) * u + w * (x + d) = u + d := by rw [hw]; field_simp; ring
      rw [e1] at h1; rw [e2] at h2
      linarith
    · simp only [add_zero]; linarith
  · linarith

/-- multiplicative four-point (TP₂) inequality for log-concave positive functions -/
theorem tp2 {F : ℝ → ℝ} (hpos : ∀ x, 0 < F x) (hc : ConcaveOn ℝ univ (fun x => Real.log (F x)))
    {u x d : ℝ} (hux : u ≤ x) (hd : 0 ≤ d) : F (x + d) * F u ≤ F x * F (u + d) := by
  have h := four_point hc hux hd
  have e : ∀ z, F z = Real.exp (Real.log (F z)) := fun z => (Real.exp_log (hpos z)).symm
  rw [e (x + d), e u, e x, e (u + d), ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.2 h

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

/-- differentiation under the convolution against a bounded continuous integrable `k`. -/
theorem conv_deriv {f f' k : ℝ → ℝ} (hfc : Continuous f) {Bf : ℝ} (hfB : ∀ x, |f x| ≤ Bf)
    (hf' : ∀ x, HasDerivWithinAt f (f' x) (Ici x) x) (hfm : Measurable f')
    (hfi : Integrable f') (hkc : Continuous k) (hki : Integrable k) {Bk : ℝ}
    (hkB : ∀ x, |k x| ≤ Bk) :
    (∀ x, HasDerivAt (fun x => ∫ y, f (x - y) * k y) (∫ y, f' (x - y) * k y) x) ∧
    Continuous (fun x => ∫ y, f' (x - y) * k y) ∧
    ∀ x, |∫ y, f' (x - y) * k y| ≤ Bk * ∫ t, |f' t| := by
  set c : ℝ → ℝ := fun x => ∫ y, f (x - y) * k y with hc
  set g : ℝ → ℝ := fun x => ∫ y, f' (x - y) * k y with hg
  have hkm : Measurable k := hkc.measurable
  have hBk : 0 ≤ Bk := (abs_nonneg _).trans (hkB 0)
  have hg' : ∀ s, g s = ∫ t, f' t * k (s - t) := by
    intro s
    have := integral_sub_left_eq_self (fun t => f' t * k (s - t)) volume s
    simp only [sub_sub_cancel] at this
    exact this
  have hgc : Continuous g := by
    have : g = fun s => ∫ t, f' t * k (s - t) := funext hg'
    rw [this]
    apply continuous_of_dominated (bound := fun t => Bk * |f' t|)
    · intro s
      exact (hfm.mul (hkm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · intro s
      refine Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hkB _) (abs_nonneg _)
    · exact hfi.abs.const_mul Bk
    · exact Eventually.of_forall fun t => continuous_const.mul
        (hkc.comp (continuous_id.sub continuous_const))
  have hgB : ∀ x, |g x| ≤ Bk * ∫ t, |f' t| := by
    intro x
    rw [hg' x, ← integral_const_mul, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (hfi.abs.const_mul Bk)
    refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hkB _) (abs_nonneg _)
  -- integrability facts
  have hfk : ∀ x, Integrable (fun y => f (x - y) * k y) := by
    intro x
    refine hki.bdd_mul (c := Bf) (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hfB _
  have hf'k : ∀ s, Integrable (fun y => f' (s - y) * k y) := by
    intro s
    have := (hfi.comp_sub_left s).bdd_mul (c := Bk) hkc.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hkB y)
    simpa [mul_comm] using this
  have hFTC : ∀ x y, f (x - y) - f (0 - y) = ∫ s in (0:ℝ)..x, f' (s - y) := by
    intro x y
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right (f := fun s => f (s - y))
    · exact (hfc.comp (continuous_id.sub continuous_const)).continuousOn
    · intro s _
      have h1 := hasDerivWithinAt_Ioi_iff_Ici.2 (hf' (s - y))
      have h2 : HasDerivWithinAt (fun s => s - y) 1 (Ioi s) s :=
        ((hasDerivAt_id s).sub_const y).hasDerivWithinAt
      have := h1.comp s h2 (fun t ht => by simp only [mem_Ioi] at ht ⊢; linarith)
      rw [mul_one] at this
      exact this
    · exact (hfi.comp_sub_right y).intervalIntegrable
  have hdiff : ∀ x, c x - c 0 = ∫ s in (0:ℝ)..x, g s := by
    intro x
    simp only [hc, hg]
    rw [← integral_sub (hfk x) (hfk 0)]
    have : ∀ y, f (x - y) * k y - f (0 - y) * k y = ∫ s in (0:ℝ)..x, f' (s - y) * k y := by
      intro y
      rw [← sub_mul, hFTC x y, intervalIntegral.integral_mul_const]
    simp_rw [this]
    symm
    apply intervalIntegral_integral_swap
    have hmeas : AEStronglyMeasurable (Function.uncurry fun s y => f' (s - y) * k y)
        ((volume.restrict (uIoc 0 x)).prod volume) :=
      ((hfm.comp (measurable_fst.sub measurable_snd)).mul
        (hkm.comp measurable_snd)).aestronglyMeasurable
    rw [integrable_prod_iff hmeas]
    constructor
    · exact Eventually.of_forall fun s => hf'k s
    · haveI : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) x)) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ, uIoc]
        simp
      apply Integrable.of_bound (C := Bk * ∫ t, |f' t|)
      · exact hmeas.norm.integral_prod_right'
      · refine Eventually.of_forall fun s => ?_
        simp only [Function.uncurry_apply_pair]
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        have : ∫ y, ‖f' (s - y) * k y‖ = ∫ t, |f' t| * |k (s - t)| := by
          have := integral_sub_left_eq_self (fun t => |f' t| * |k (s - t)|) volume s
          simp only [sub_sub_cancel] at this
          rw [← this]; congr 1; funext y; rw [Real.norm_eq_abs, abs_mul]
        rw [this, ← integral_const_mul]
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
          (hfi.abs.const_mul Bk)
        refine Eventually.of_forall fun t => ?_
        simp only
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hkB _) (abs_nonneg _)
  refine ⟨fun x => ?_, hgc, hgB⟩
  have h := ((hgc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add (c 0)
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall fun y => by
    show c y = c 0 + ∫ s in (0:ℝ)..y, g s
    rw [← hdiff y]; ring

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

end LiqD2Aux

open LiqD2Aux in
theorem solution (f h : ℝ → ℝ)
    (hfpos : ∀ x, 0 < f x) (hfint : MeasureTheory.Integrable f) (hfmass : ∫ x, f x = 1)
    (hflc : ConcaveOn ℝ Set.univ (fun x => Real.log (f x)))
    (hhpos : ∀ x, 0 < h x) (hhint : MeasureTheory.Integrable h) (hhmass : ∫ x, h x = 1)
    (hhlc : ConcaveOn ℝ Set.univ (fun x => Real.log (h x)))
    (f' : ℝ → ℝ) (hf' : ∀ x, HasDerivWithinAt f (f' x) (Set.Ici x) x) :
    ((∀ x, 0 < ∫ y, f (x - y) * h y) ∧
      MeasureTheory.Integrable (fun x => ∫ y, f (x - y) * h y) ∧
      ∫ x, (∫ y, f (x - y) * h y) = 1 ∧
      ConcaveOn ℝ Set.univ (fun x => Real.log (∫ y, f (x - y) * h y)) ∧
      ContDiff ℝ 1 (fun x => ∫ y, f (x - y) * h y) ∧
      (∃ B : ℝ, ∀ x, |deriv (fun x => ∫ y, f (x - y) * h y) x| ≤ B) ∧
      ∀ x, deriv (fun x => ∫ y, f (x - y) * h y) x = ∫ y, f' (x - y) * h y) ∧
    (MeasureTheory.Integrable (fun x => ∫ y, f (x - y) * (y * h y)) ∧
      ContDiff ℝ 1 (fun x => ∫ y, f (x - y) * (y * h y)) ∧
      (∃ B : ℝ, ∀ x, |deriv (fun x => ∫ y, f (x - y) * (y * h y)) x| ≤ B) ∧
      ∀ x, deriv (fun x => ∫ y, f (x - y) * (y * h y)) x = ∫ y, f' (x - y) * (y * h y)) := by
  obtain ⟨-, ⟨Cf, εf, hCf, hεf, hftail⟩, ⟨f'', hf'', xs, hxs1, hxs2⟩⟩ :=
    LiqProvision.Oligopoly.proposition_D_1 f hfpos hfint hfmass hflc
  obtain ⟨-, ⟨Ch, εh, hCh, hεh, hhtail⟩, -⟩ :=
    LiqProvision.Oligopoly.proposition_D_1 h hhpos hhint hhmass hhlc
  have hfc := logconcave_continuous hfpos hflc
  have hhc := logconcave_continuous hhpos hhlc
  have heq' : ∀ x, f' x = f'' x := fun x =>
    (uniqueDiffWithinAt_Ici x).eq_deriv _ (hf' x) (hf'' x)
  have hfm : Measurable f' := rderiv_measurable hfc hf'
  have hfi : Integrable f' := rderiv_integrable hfc hfpos hf' xs
    (fun x hx => heq' x ▸ hxs1 x hx) (fun x hx => heq' x ▸ hxs2 x hx)
  have hfB : ∀ x, |f x| ≤ Cf := by
    intro x
    rw [abs_of_pos (hfpos x)]
    calc f x ≤ Cf * Real.exp (-εf * |x|) := hftail x
      _ ≤ Cf * 1 := by
        apply mul_le_mul_of_nonneg_left _ hCf.le
        rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg x]
      _ = Cf := mul_one _
  have hhB : ∀ x, |h x| ≤ Ch := by
    intro x
    rw [abs_of_pos (hhpos x)]
    calc h x ≤ Ch * Real.exp (-εh * |x|) := hhtail x
      _ ≤ Ch * 1 := by
        apply mul_le_mul_of_nonneg_left _ hCh.le
        rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg x]
      _ = Ch := mul_one _
  -- the moment function y h(y)
  have hyhB : ∀ y, |y * h y| ≤ Ch / εh := by
    intro y
    rw [abs_mul, abs_of_pos (hhpos y), le_div_iff₀ hεh]
    have h1 := hhtail y
    have h2 : εh * |y| ≤ Real.exp (εh * |y|) := by
      have := Real.add_one_le_exp (εh * |y|); linarith
    have h3 : Real.exp (-εh * |y|) * Real.exp (εh * |y|) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : |y| * h y * εh ≤ |y| * (Ch * Real.exp (-εh * |y|)) * εh :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg y)) hεh.le
    have h5 : |y| * (Ch * Real.exp (-εh * |y|)) * εh =
        Ch * Real.exp (-εh * |y|) * (εh * |y|) := by ring
    have h6 : Ch * Real.exp (-εh * |y|) * (εh * |y|) ≤
        Ch * Real.exp (-εh * |y|) * Real.exp (εh * |y|) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hyhc : Continuous (fun y => y * h y) := continuous_id.mul hhc
  have hyhi : Integrable (fun y => y * h y) := by
    have hexp := (integrable_exp_neg_abs (a := εh / 2) (by positivity)).const_mul
      (Ch * (2 / εh))
    refine Integrable.mono' hexp hyhc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hhpos y)]
    have h1 := hhtail y
    have h2 : εh / 2 * |y| ≤ Real.exp (εh / 2 * |y|) := by
      have := Real.add_one_le_exp (εh / 2 * |y|); linarith
    have h3 : Real.exp (-εh * |y|) = Real.exp (-(εh / 2) * |y|) * Real.exp (-(εh / 2) * |y|) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (-(εh / 2) * |y|) * Real.exp (εh / 2 * |y|) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : |y| ≤ 2 / εh * Real.exp (εh / 2 * |y|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hεh]; linarith
    have hE := Real.exp_pos (-(εh / 2) * |y|)
    calc |y| * h y ≤ |y| * (Ch * Real.exp (-εh * |y|)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg y)
      _ = Ch * Real.exp (-(εh / 2) * |y|) * (|y| * Real.exp (-(εh / 2) * |y|)) := by
          rw [h3]; ring
      _ ≤ Ch * Real.exp (-(εh / 2) * |y|) *
            (2 / εh * Real.exp (εh / 2 * |y|) * Real.exp (-(εh / 2) * |y|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h5 hE.le
      _ = Ch * (2 / εh) * Real.exp (-(εh / 2) * |y|) := by
          rw [mul_assoc (2 / εh), mul_comm (Real.exp (εh / 2 * |y|)), h4]; ring
  obtain ⟨hd1, hgc1, hgB1⟩ := conv_deriv hfc hfB hf' hfm hfi hhc hhint hhB
  obtain ⟨hd2, hgc2, hgB2⟩ := conv_deriv hfc hfB hf' hfm hfi hyhc hyhi hyhB
  set c : ℝ → ℝ := fun x => ∫ y, f (x - y) * h y with hc
  have hcconv : c = MeasureTheory.convolution h f (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    simp only [hc, MeasureTheory.convolution, ContinuousLinearMap.mul_apply']
    congr 1; funext y; ring
  have hc2conv : (fun x => ∫ y, f (x - y) * (y * h y)) =
      MeasureTheory.convolution (fun y => y * h y) f (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    simp only [MeasureTheory.convolution, ContinuousLinearMap.mul_apply']
    congr 1; funext y; ring
  have hfk : ∀ x, Integrable (fun y => f (x - y) * h y) := by
    intro x
    refine hhint.bdd_mul (c := Cf) (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hfB _
  have hcpos : ∀ x, 0 < c x := by
    intro x
    simp only [hc]
    rw [integral_pos_iff_support_of_nonneg (fun y => (mul_pos (hfpos _) (hhpos _)).le) (hfk x)]
    have : Function.support (fun y => f (x - y) * h y) = univ := by
      ext y; simp [(hfpos _).ne', (hhpos _).ne']
    rw [this]; simp
  -- the four-point inequality for c
  have hcab : ∀ a b, c (a - b) = ∫ z, f (a - z) * h (z - b) := by
    intro a b
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun y => f (a - b - y) * h y) b
    simp only [hc]; rw [← this]
    congr 1; funext z; congr 2; ring
  have hint_ab : ∀ a b, Integrable (fun z => f (a - z) * h (z - b)) := by
    intro a b
    refine (hhint.comp_sub_right b).bdd_mul (c := Cf)
      (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hfB _
  have hCB : ∀ a₁ a₂ b₁ b₂, a₁ ≤ a₂ → b₁ ≤ b₂ →
      c (a₁ - b₂) * c (a₂ - b₁) ≤ c (a₁ - b₁) * c (a₂ - b₂) := by
    intro a₁ a₂ b₁ b₂ ha hb
    set A₁ : ℝ → ℝ := fun z => f (a₁ - z)
    set A₂ : ℝ → ℝ := fun z => f (a₂ - z)
    set B₁ : ℝ → ℝ := fun z => h (z - b₁)
    set B₂ : ℝ → ℝ := fun z => h (z - b₂)
    set G : ℝ × ℝ → ℝ := fun p => (A₁ p.1 * B₁ p.1) * (A₂ p.2 * B₂ p.2) -
      (A₁ p.1 * B₂ p.1) * (A₂ p.2 * B₁ p.2) with hG
    have hI1 : Integrable (fun p : ℝ × ℝ => (A₁ p.1 * B₁ p.1) * (A₂ p.2 * B₂ p.2))
        (volume.prod volume) := (hint_ab a₁ b₁).mul_prod (hint_ab a₂ b₂)
    have hI2 : Integrable (fun p : ℝ × ℝ => (A₁ p.1 * B₂ p.1) * (A₂ p.2 * B₁ p.2))
        (volume.prod volume) := (hint_ab a₁ b₂).mul_prod (hint_ab a₂ b₁)
    have hGI : Integrable G (volume.prod volume) := hI1.sub hI2
    have hP : c (a₁ - b₁) * c (a₂ - b₂) - c (a₁ - b₂) * c (a₂ - b₁) =
        ∫ p, G p ∂(volume.prod volume) := by
      rw [hcab, hcab, hcab, hcab, integral_sub hI1 hI2,
        integral_prod_mul (fun z => A₁ z * B₁ z) (fun z => A₂ z * B₂ z),
        integral_prod_mul (fun z => A₁ z * B₂ z) (fun z => A₂ z * B₁ z)]
    have hsw : ∫ p, G p.swap ∂(volume.prod volume) = ∫ p, G p ∂(volume.prod volume) :=
      integral_prod_swap G
    have hpt : ∀ p : ℝ × ℝ, 0 ≤ G p + G p.swap := by
      rintro ⟨z₁, z₂⟩
      have key : G (z₁, z₂) + G (z₁, z₂).swap =
          (A₁ z₁ * A₂ z₂ - A₁ z₂ * A₂ z₁) * (B₁ z₁ * B₂ z₂ - B₂ z₁ * B₁ z₂) := by
        simp only [hG, Prod.swap]; ring
      rw [key]
      -- TP2 facts
      have tpA : ∀ z₁ z₂, z₁ ≤ z₂ → A₁ z₂ * A₂ z₁ ≤ A₁ z₁ * A₂ z₂ := by
        intro z₁ z₂ hz
        have := tp2 hfpos hflc (u := a₁ - z₂) (x := a₁ - z₁) (d := a₂ - a₁) (by linarith)
          (by linarith)
        have e1 : a₁ - z₁ + (a₂ - a₁) = a₂ - z₁ := by ring
        have e2 : a₁ - z₂ + (a₂ - a₁) = a₂ - z₂ := by ring
        rw [e1, e2] at this
        simp only [A₁, A₂]; linarith
      have tpB : ∀ z₁ z₂, z₁ ≤ z₂ → B₂ z₁ * B₁ z₂ ≤ B₁ z₁ * B₂ z₂ := by
        intro z₁ z₂ hz
        have := tp2 hhpos hhlc (u := z₁ - b₂) (x := z₂ - b₂) (d := b₂ - b₁) (by linarith)
          (by linarith)
        have e1 : z₂ - b₂ + (b₂ - b₁) = z₂ - b₁ := by ring
        have e2 : z₁ - b₂ + (b₂ - b₁) = z₁ - b₁ := by ring
        rw [e1, e2] at this
        simp only [B₁, B₂]; linarith
      rcases le_total z₁ z₂ with hz | hz
      · exact mul_nonneg (by linarith [tpA z₁ z₂ hz]) (by linarith [tpB z₁ z₂ hz])
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [tpA z₂ z₁ hz])
          (by linarith [tpB z₂ z₁ hz])
    have hsum : 0 ≤ ∫ p, (G p + G p.swap) ∂(volume.prod volume) :=
      integral_nonneg hpt
    have hGsI : Integrable (fun p : ℝ × ℝ => G p.swap) (volume.prod volume) := hGI.swap
    rw [integral_add hGI hGsI, hsw] at hsum
    linarith
  have hfour : ∀ u x d, u ≤ x → 0 ≤ d → c (x + d) * c u ≤ c x * c (u + d) := by
    intro u x d hux hd
    have := hCB u x (-d) 0 hux (by linarith)
    simp only [sub_zero, sub_neg_eq_add] at this
    linarith [mul_comm (c u) (c (x + d)), mul_comm (c (u + d)) (c x)]
  -- log-concavity via the derivative
  set g : ℝ → ℝ := fun x => ∫ y, f' (x - y) * h y with hg
  have hcd : ∀ x, HasDerivAt c (g x) x := hd1
  have hratio : ∀ u x, u ≤ x → g x * c u ≤ c x * g u := by
    intro u x hux
    have t1 := (hcd x).tendsto_slope_zero_right
    have t2 := (hcd u).tendsto_slope_zero_right
    have tl := t1.const_mul (c u)
    have tr := t2.const_mul (c x)
    rw [mul_comm] at tl
    refine le_of_tendsto_of_tendsto tl tr ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hd0 : 0 < d := hd
    simp only [smul_eq_mul]
    have := hfour u x d hux hd0.le
    have hdi : 0 < d⁻¹ := inv_pos.2 hd0
    nlinarith [mul_le_mul_of_nonneg_left (show c (x + d) * c u - c x * c u ≤
      c x * c (u + d) - c x * c u by linarith) hdi.le]
  have hlogc : ConcaveOn ℝ univ (fun x => Real.log (c x)) := by
    have hGd : ∀ x, HasDerivAt (fun x => Real.log (c x)) (g x / c x) x :=
      fun x => (hcd x).log (hcpos x).ne'
    have hderiv : deriv (fun x => Real.log (c x)) = fun x => g x / c x :=
      funext fun x => (hGd x).deriv
    apply AntitoneOn.concaveOn_of_deriv convex_univ
    · exact fun x _ => (hGd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hGd x).differentiableAt.differentiableWithinAt
    · rw [hderiv]
      intro u _ x _ hux
      simp only
      rw [div_le_div_iff₀ (hcpos x) (hcpos u)]
      have := hratio u x hux
      linarith
  have hderiv1 : deriv c = g := funext fun x => (hcd x).deriv
  have hderiv2 : deriv (fun x => ∫ y, f (x - y) * (y * h y)) =
      fun x => ∫ y, f' (x - y) * (y * h y) := funext fun x => (hd2 x).deriv
  refine ⟨⟨hcpos, ?_, ?_, hlogc, ?_, ⟨_, fun x => by rw [hderiv1]; exact hgB1 x⟩,
    fun x => by rw [hderiv1]⟩, ⟨?_, ?_, ⟨_, fun x => by rw [hderiv2]; exact hgB2 x⟩,
    fun x => by rw [hderiv2]⟩⟩
  · rw [hcconv]; exact hhint.integrable_convolution _ hfint
  · rw [hcconv, integral_convolution _ hhint hfint, hhmass, hfmass]; simp
  · rw [contDiff_one_iff_deriv]
    exact ⟨fun x => (hcd x).differentiableAt, hderiv1 ▸ hgc1⟩
  · rw [hc2conv]; exact hyhi.integrable_convolution _ hfint
  · rw [contDiff_one_iff_deriv]
    exact ⟨fun x => (hd2 x).differentiableAt, hderiv2 ▸ hgc2⟩
