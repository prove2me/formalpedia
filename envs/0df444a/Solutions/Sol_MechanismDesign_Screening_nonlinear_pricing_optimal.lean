-- Prove2me | solution 1 for MechanismDesign.Screening.nonlinear_pricing_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:16:07.935273+00:00
-- url     : https://prove2.me/submissions/bdddb10a-7b04-4430-bd8e-8499577b08ab

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model
import Definitions.Def_MechanismDesign_Screening_NonlinearPricing

open MeasureTheory

namespace MechanismDesign.Screening

section Abstract
variable {Q T : ℝ → ℝ} {a b : ℝ}

def ICabs (Q T : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∀ x' ∈ Set.Icc a b, x * Q x' - T x' ≤ x * Q x - T x

lemma abs_mono (h : ICabs Q T a b) : MonotoneOn Q (Set.Icc a b) := by
  intro x hx y hy hxy
  have h1 := h x hx y hy
  have h2 := h y hy x hx
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · nlinarith

lemma abs_sub (h : ICabs Q T a b) {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    (y - x) * Q x ≤ (y * Q y - T y) - (x * Q x - T x) := by
  have := h y hy x hx; nlinarith

lemma abs_lip (h : ICabs Q T a b) (hab : a ≤ b) :
    LipschitzOnWith (Real.toNNReal (max |Q a| |Q b|)) (fun x => x * Q x - T x) (Set.Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hm := abs_mono h
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have bx : |Q x| ≤ max |Q a| |Q b| := by
    have := hm ha hx hx.1; have := hm hx hb hx.2
    rw [abs_le]; constructor
    · have := le_max_left |Q a| |Q b|; have := neg_abs_le (Q a); linarith
    · have := le_max_right |Q a| |Q b|; have := le_abs_self (Q b); linarith
  have byy : |Q y| ≤ max |Q a| |Q b| := by
    have := hm ha hy hy.1; have := hm hy hb hy.2
    rw [abs_le]; constructor
    · have := le_max_left |Q a| |Q b|; have := neg_abs_le (Q a); linarith
    · have := le_max_right |Q a| |Q b|; have := le_abs_self (Q b); linarith
  have h1 := abs_sub h hx hy
  have h2 := abs_sub h hy hx
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_trans (abs_nonneg _) (le_max_left _ _))]
  set M := max |Q a| |Q b|
  rw [abs_le]
  rcases le_total x y with hxy | hxy
  · have e1 : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e1]
    have := abs_le.1 bx; have := abs_le.1 byy
    constructor <;> nlinarith
  · have e1 : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [e1]
    have := abs_le.1 bx; have := abs_le.1 byy
    constructor <;> nlinarith

/-- monotone extension -/
noncomputable def ext (Q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) : ℝ → ℝ :=
  fun x => Q (Set.projIcc a b hab x)

lemma ext_mono (h : ICabs Q T a b) (hab : a ≤ b) : Monotone (ext Q a b hab) := by
  intro x y hxy
  exact abs_mono h (Set.projIcc a b hab x).2 (Set.projIcc a b hab y).2
    (Set.monotone_projIcc hab hxy)

lemma ext_eq (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : ext Q a b hab x = Q x := by
  simp [ext, Set.projIcc_of_mem hab hx]

lemma abs_hasDerivAt (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hc : ContinuousAt (ext Q a b hab) x) :
    HasDerivAt (fun x => x * Q x - T x) (Q x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∈ Set.Icc a b :=
    nhdsWithin_le_nhds (Icc_mem_nhds hx.1 hx.2)
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Filter.Tendsto (fun y => dist (ext Q a b hab y) (Q x)) (nhdsWithin x {x}ᶜ)
      (nhds 0) := by
    have : Filter.Tendsto (ext Q a b hab) (nhdsWithin x {x}ᶜ) (nhds (ext Q a b hab x)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [ext_eq hab hxI] at this
    exact (tendsto_iff_dist_tendsto_zero).1 this
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) _ hlim
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyx
  rw [ext_eq hab hy, slope_def_field, Real.dist_eq, Real.dist_eq]
  have hyx' : y - x ≠ 0 := sub_ne_zero.2 hyx
  have h1 := abs_sub h hxI hy
  have h2 := abs_sub h hy hxI
  have hm := abs_mono h
  obtain ⟨s, hsD⟩ : ∃ s, (y * Q y - T y) - (x * Q x - T x) = s * (y - x) :=
    ⟨_, (div_mul_cancel₀ _ hyx').symm⟩
  rw [hsD, mul_div_cancel_right₀ _ hyx']
  rw [hsD] at h1
  have h2' : (x - y) * Q y ≤ -(s * (y - x)) := by linarith
  clear h2
  rcases lt_or_gt_of_ne hyx with hlt | hgt
  · have hQ := hm hy hxI hlt.le
    have b1 : s ≤ Q x := by nlinarith
    have b2 : Q y ≤ s := by nlinarith [h2']
    rw [abs_le]; constructor <;> rw [abs_of_nonpos (by linarith)] <;> linarith
  · have hQ := hm hxI hy hgt.le
    have b1 : Q x ≤ s := by nlinarith
    have b2 : s ≤ Q y := by nlinarith [h2']
    rw [abs_le]; constructor <;> rw [abs_of_nonneg (by linarith)] <;> linarith

lemma abs_payoff (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    x * Q x - T x = (a * Q a - T a) + ∫ y in a..x, Q y := by
  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hx.2
  have key := integral_eq_of_hasDerivAt_off_countable_of_le (fun x => x * Q x - T x) Q hx.1
    (ext_mono h hab).countable_not_continuousAt
    ((abs_lip h hab).continuousOn.mono hsub)
    (fun y hy => abs_hasDerivAt h hab ⟨hy.1.1, lt_of_lt_of_le hy.1.2 hx.2⟩ (by
      by_contra hc; exact hy.2 hc))
    (by
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hx.1]; exact (abs_mono h).mono hsub)
  rw [key]; ring


lemma abs_ic_of_formula (hab : a ≤ b) (hm : MonotoneOn Q (Set.Icc a b))
    (hT : ∀ x ∈ Set.Icc a b, T x = T a + (x * Q x - a * Q a) - ∫ y in a..x, Q y) :
    ICabs Q T a b := by
  intro x hx x' hx'
  have hint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, IntervalIntegrable Q volume u v := by
    intro u hu v hv
    apply MonotoneOn.intervalIntegrable
    exact hm.mono (Set.uIcc_subset_Icc hu hv)
  have eT := hT x hx
  have eT' := hT x' hx'
  have hsplit : (∫ y in a..x, Q y) - ∫ y in a..x', Q y = ∫ y in x'..x, Q y := by
    rw [intervalIntegral.integral_interval_sub_left (hint _ ⟨le_rfl, hab⟩ _ hx)
      (hint _ ⟨le_rfl, hab⟩ _ hx')]
  have key : (x - x') * Q x' ≤ ∫ y in x'..x, Q y := by
    rcases le_total x' x with hle | hle
    · have : ∫ y in x'..x, Q x' ≤ ∫ y in x'..x, Q y := by
        apply intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint _ hx' _ hx)
        intro y hy
        exact hm hx' ⟨le_trans hx'.1 hy.1, le_trans hy.2 hx.2⟩ hy.1
      simpa [mul_comm] using this
    · have : ∫ y in x..x', Q y ≤ ∫ y in x..x', Q x' := by
        apply intervalIntegral.integral_mono_on hle (hint _ hx _ hx') intervalIntegrable_const
        intro y hy
        exact hm ⟨le_trans hx.1 hy.1, le_trans hy.2 hx'.2⟩ hx' hy.2
      rw [intervalIntegral.integral_symm]
      simp at this
      nlinarith
  linarith

lemma ext_mono_of (hab : a ≤ b) (hm : MonotoneOn Q (Set.Icc a b)) : Monotone (ext Q a b hab) := by
  intro x y hxy
  exact hm (Set.projIcc a b hab x).2 (Set.projIcc a b hab y).2 (Set.monotone_projIcc hab hxy)

lemma ext_bound (hab : a ≤ b) (hm : MonotoneOn Q (Set.Icc a b)) (y : ℝ) :
    |ext Q a b hab y| ≤ |Q a| + |Q b| := by
  have hp := (Set.projIcc a b hab y).2
  have h1 : Q a ≤ ext Q a b hab y := hm ⟨le_rfl, hab⟩ hp hp.1
  have h2 : ext Q a b hab y ≤ Q b := hm hp ⟨hab, le_rfl⟩ hp.2
  rw [abs_le]; constructor
  · have := neg_abs_le (Q a); have := abs_nonneg (Q b); linarith
  · have := le_abs_self (Q b); have := abs_nonneg (Q a); linarith

lemma int_ext_eq (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∫ y in a..x, ext Q a b hab y = ∫ y in a..x, Q y := by
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hx.1] at hy
  exact ext_eq hab ⟨hy.1, hy.2.trans hx.2⟩

lemma abs_T_eq (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    T x = x * ext Q a b hab x - (∫ y in a..x, ext Q a b hab y) - (a * Q a - T a) := by
  have := abs_payoff h hab hx
  rw [ext_eq hab hx, int_ext_eq hab hx]
  linarith

lemma abs_T_meas (h : ICabs Q T a b) (hab : a ≤ b) :
    AEStronglyMeasurable T (volume.restrict (Set.Ioc a b)) := by
  set e := ext Q a b hab
  have hem : Monotone e := ext_mono h hab
  have hcont : Continuous (fun θ => ∫ x in a..θ, e x) :=
    intervalIntegral.continuous_primitive (fun a b => hem.intervalIntegrable) a
  have hmeas : Measurable (fun x => x * e x - (∫ y in a..x, e y) - (a * Q a - T a)) := by
    have := hem.measurable
    fun_prop
  refine (hmeas.aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact (abs_T_eq h hab (Set.Ioc_subset_Icc_self hθ)).symm

end Abstract

variable {θlo θhi : ℝ}

lemma ii_bdd_mul {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b))) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc a b, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * f x) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hf ⊢
  refine Integrable.bdd_mul (c := C) hf hg ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Set.Ioc_subset_Icc_self hx)

lemma one_sub_F (D : TypeDistribution θlo θhi) {y : ℝ} (hy : y ∈ Set.Icc θlo θhi) :
    ∫ x in y..θhi, D.f x = 1 - D.F y := by
  have hab := D.lo_lt_hi.le
  have h1 : IntervalIntegrable D.f volume θlo θhi := D.f_integrable
  have h2 : IntervalIntegrable D.f volume θlo y := D.f_integrable.mono_set (by
    rw [Set.uIcc_of_le hy.1, Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc le_rfl hy.2)
  rw [D.F_eq y hy, ← D.f_total, intervalIntegral.integral_interval_sub_left h1 h2]

lemma F_contOn (D : TypeDistribution θlo θhi) : ContinuousOn D.F (Set.uIcc θlo θhi) := by
  have hab := D.lo_lt_hi.le
  have := intervalIntegral.continuousOn_primitive_interval' D.f_integrable Set.left_mem_uIcc
    (μ := volume)
  refine this.congr ?_
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  exact D.F_eq y hy

lemma fubini_D (D : TypeDistribution θlo θhi) (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hb : ∀ y, |g y| ≤ C) :
    ∫ x in θlo..θhi, (∫ y in θlo..x, g y) * D.f x
      = ∫ y in θlo..θhi, g y * (1 - D.F y) := by
  have hab := D.lo_lt_hi.le
  set S := Set.Icc θlo θhi with hS
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  have hfS : Integrable D.f (volume.restrict S) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 D.f_integrable
    exact (integrableOn_Icc_iff_integrableOn_Ioc (ha := by simp)).2 this
  let k : ℝ → ℝ → ℝ := fun x y => (if y ≤ x then g y else 0) * D.f x
  have hkm : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict S).prod (volume.restrict S)) := by
    apply AEStronglyMeasurable.mul
    · exact (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hg.comp measurable_snd) measurable_const).aestronglyMeasurable
    · exact hfS.aestronglyMeasurable.comp_fst
  have hk : Integrable (Function.uncurry k) ((volume.restrict S).prod (volume.restrict S)) := by
    have hb' : Integrable (fun p : ℝ × ℝ => D.f p.1 * C)
        ((volume.restrict S).prod (volume.restrict S)) :=
      hfS.mul_prod (integrable_const C)
    refine hb'.norm.mono' hkm (Filter.Eventually.of_forall ?_)
    intro p
    simp only [Function.uncurry, k, norm_mul, Real.norm_eq_abs, abs_abs, abs_of_nonneg hC0]
    have : |(if p.2 ≤ p.1 then g p.2 else 0)| ≤ C := by
      split_ifs
      · exact hb _
      · simpa using hC0
    rw [mul_comm (|D.f p.1|)]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hL : ∀ x ∈ S, ∫ y in S, k x y = (∫ y in θlo..x, g y) * D.f x := by
    intro x hx
    simp only [k]
    rw [integral_mul_const]
    congr 1
    have : (fun y => if y ≤ x then g y else 0) = (Set.Iic x).indicator g := by
      funext y; simp [Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Iic]
    have hset : S ∩ Set.Iic x = Set.Icc θlo x := by
      ext y; simp only [hS, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hx.2⟩, h3⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1]
  have hR : ∀ y ∈ S, ∫ x in S, k x y = g y * (1 - D.F y) := by
    intro y hy
    simp only [k]
    have : (fun x => (if y ≤ x then g y else 0) * D.f x)
        = (Set.Ici y).indicator (fun x => g y * D.f x) := by
      funext x; simp [Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Ici, integral_const_mul]
    have hset : S ∩ Set.Ici y = Set.Icc y θhi := by
      ext x; simp only [hS, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨le_trans hy.1 h1, h3⟩, h1⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.2,
      one_sub_F D hy]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [← setIntegral_congr_fun measurableSet_Icc hL, integral_integral_swap hk,
    setIntegral_congr_fun measurableSet_Icc hR]

/-- the virtual-surplus integrand -/
noncomputable def Jint (D : TypeDistribution θlo θhi) (E : NonlinearEnv θhi)
    (m : QuantityMechanism θlo θhi) (θ : ℝ) : ℝ :=
  (E.ν (m.q θ) * virtualValuation D θ - E.c * m.q θ) * D.f θ

lemma profit_eq (D : TypeDistribution θlo θhi) (E : NonlinearEnv θhi)
    (hνmono : StrictMonoOn E.ν (Set.Ici 0))
    (m : QuantityMechanism θlo θhi) (hic : m.IsIC E) :
    IntervalIntegrable (Jint D E m) volume θlo θhi ∧
    expectedProfit D E m = (∫ θ in θlo..θhi, Jint D E m θ) - (θlo * E.ν (m.q θlo) - m.t θlo) := by
  have hlt := D.lo_lt_hi
  have hab := hlt.le
  have hlo := D.lo_nonneg
  set Q : ℝ → ℝ := fun θ => E.ν (m.q θ) with hQ
  have h : ICabs Q m.t θlo θhi := fun x hx x' hx' => hic x hx x' hx'
  have hQm : MonotoneOn Q (Set.Icc θlo θhi) := abs_mono h
  have hqm : MonotoneOn m.q (Set.Icc θlo θhi) := by
    intro x hx y hy hxy
    have := hQm hx hy hxy
    exact (hνmono.le_iff_le (m.q_nonneg x hx) (m.q_nonneg y hy)).1 this
  set Qe := ext Q θlo θhi hab with hQe
  set qe := ext m.q θlo θhi hab with hqe
  have hQem : Monotone Qe := ext_mono_of hab hQm
  have hqem : Monotone qe := ext_mono_of hab hqm
  set BQ := |Q θlo| + |Q θhi|
  set Bq := |m.q θlo| + |m.q θhi|
  have hBQ : ∀ y, |Qe y| ≤ BQ := ext_bound hab hQm
  have hBq : ∀ y, |qe y| ≤ Bq := ext_bound hab hqm
  have hBQ0 : 0 ≤ BQ := (abs_nonneg _).trans (hBQ 0)
  have hBq0 : 0 ≤ Bq := (abs_nonneg _).trans (hBq 0)
  set δ := θlo * Q θlo - m.t θlo with hδ
  have hT : ∀ θ ∈ Set.Icc θlo θhi, m.t θ = θ * Qe θ - (∫ y in θlo..θ, Qe y) - δ :=
    fun θ hθ => abs_T_eq h hab hθ
  have hPc : Continuous (fun θ => ∫ y in θlo..θ, Qe y) :=
    intervalIntegral.continuous_primitive (fun a b => hQem.intervalIntegrable) θlo
  -- integrability of the pieces
  have iA : IntervalIntegrable (fun θ => (θ * Qe θ) * D.f θ) volume θlo θhi := by
    refine ii_bdd_mul hab D.f_integrable
      ((measurable_id.mul hQem.measurable).aestronglyMeasurable) (θhi * BQ) ?_
    intro x hx
    rw [abs_mul, abs_of_nonneg (hlo.trans hx.1)]
    exact mul_le_mul hx.2 (hBQ x) (abs_nonneg _) (hlo.trans hab)
  have iB : IntervalIntegrable (fun θ => (∫ y in θlo..θ, Qe y) * D.f θ) volume θlo θhi := by
    refine ii_bdd_mul hab D.f_integrable hPc.aestronglyMeasurable (BQ * |θhi - θlo|) ?_
    intro x hx
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := θlo) (b := x) (C := BQ)
      (f := Qe) (fun y _ => by rw [Real.norm_eq_abs]; exact hBQ y)
    rw [Real.norm_eq_abs] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hBQ0)
    rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith)]
    linarith [hx.2]
  have iC : IntervalIntegrable (fun θ => δ * D.f θ) volume θlo θhi := D.f_integrable.const_mul δ
  have iD : IntervalIntegrable (fun θ => (E.c * qe θ) * D.f θ) volume θlo θhi := by
    refine ii_bdd_mul hab D.f_integrable
      ((measurable_const.mul hqem.measurable).aestronglyMeasurable) (E.c * Bq) ?_
    intro x _
    rw [abs_mul, abs_of_pos E.c_pos]
    exact mul_le_mul_of_nonneg_left (hBq x) E.c_pos.le
  have iQF : IntervalIntegrable (fun θ => Qe θ * (1 - D.F θ)) volume θlo θhi :=
    hQem.intervalIntegrable.mul_continuousOn (continuousOn_const.sub (F_contOn D))
  -- the profit
  have hprof : expectedProfit D E m = ∫ θ in θlo..θhi,
      ((θ * Qe θ) * D.f θ - (∫ y in θlo..θ, Qe y) * D.f θ - δ * D.f θ - (E.c * qe θ) * D.f θ) := by
    unfold expectedProfit
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    simp only
    rw [hT θ hθ, hqe, ext_eq hab hθ]
    ring
  have hJ : ∀ θ ∈ Set.Icc θlo θhi, Jint D E m θ
      = (θ * Qe θ) * D.f θ - Qe θ * (1 - D.F θ) - (E.c * qe θ) * D.f θ := by
    intro θ hθ
    have hf := (D.f_pos θ hθ).ne'
    simp only [Jint, virtualValuation]
    rw [hQe, hqe, ext_eq hab hθ, ext_eq hab hθ]
    field_simp
    ring
  have iJ' : IntervalIntegrable
      (fun θ => (θ * Qe θ) * D.f θ - Qe θ * (1 - D.F θ) - (E.c * qe θ) * D.f θ)
      volume θlo θhi := (iA.sub iQF).sub iD
  have iJ : IntervalIntegrable (Jint D E m) volume θlo θhi := by
    refine iJ'.congr_uIoo ?_
    intro θ hθ
    rw [Set.uIoo_of_le hab] at hθ
    exact (hJ θ (Set.Ioo_subset_Icc_self hθ)).symm
  refine ⟨iJ, ?_⟩
  have hJint : ∫ θ in θlo..θhi, Jint D E m θ = ∫ θ in θlo..θhi,
      ((θ * Qe θ) * D.f θ - Qe θ * (1 - D.F θ) - (E.c * qe θ) * D.f θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    exact hJ θ hθ
  rw [hprof, hJint]
  rw [intervalIntegral.integral_sub ((iA.sub iB).sub iC) iD,
    intervalIntegral.integral_sub (iA.sub iB) iC, intervalIntegral.integral_sub iA iB,
    intervalIntegral.integral_sub (iA.sub iQF) iD, intervalIntegral.integral_sub iA iQF,
    intervalIntegral.integral_const_mul, D.f_total,
    fubini_D D Qe hQem.measurable BQ hBQ]
  ring

theorem nonlinear_pricing_optimal_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (E : NonlinearEnv θhi) (hreg : IsRegular D) (m : QuantityMechanism θlo θhi)
    (hq : ∀ θ ∈ Set.Icc θlo θhi,
      (deriv E.ν 0 * virtualValuation D θ ≤ E.c → m.q θ = 0) ∧
      (E.c < deriv E.ν 0 * virtualValuation D θ →
        deriv E.ν (m.q θ) * virtualValuation D θ = E.c))
    (ht : ∀ θ ∈ Set.Icc θlo θhi, m.t θ = θ * E.ν (m.q θ) - ∫ x in θlo..θ, E.ν (m.q x)) :
    m.IsIC E ∧ m.IsIR E ∧
      ∀ m' : QuantityMechanism θlo θhi, m'.IsIC E → m'.IsIR E →
        expectedProfit D E m' ≤ expectedProfit D E m := by
  have hlt := D.lo_lt_hi
  have hab := hlt.le
  have hlo := D.lo_nonneg
  have hν'c : Continuous (deriv E.ν) := E.ν'_differentiable.continuous
  have hνc : Continuous E.ν := E.ν_differentiable.continuous
  have hν'anti : StrictAntiOn (deriv E.ν) (Set.Ici 0) :=
    strictAntiOn_of_deriv_neg (convex_Ici 0) hν'c.continuousOn
      (fun x hx => E.ν''_neg x (by rw [interior_Ici] at hx; exact le_of_lt hx))
  have hνmono : StrictMonoOn E.ν (Set.Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hνc.continuousOn
      (fun x hx => E.ν'_pos x (by rw [interior_Ici] at hx; exact le_of_lt hx))
  have hν0 : ∀ x, 0 ≤ x → 0 ≤ E.ν x := by
    intro x hx
    have := hνmono.monotoneOn (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 le_rfl) (show x ∈ Set.Ici 0 from hx) hx
    rwa [E.ν_zero] at this
  have htan : ∀ x y, 0 ≤ x → 0 ≤ y → E.ν x ≤ E.ν y + deriv E.ν y * (x - y) := by
    intro x y hx hy
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope E.ν hxy hνc.continuousOn
        E.ν_differentiable.differentiableOn
      rw [eq_div_iff (sub_ne_zero.2 hxy.ne')] at hd
      have : deriv E.ν y ≤ deriv E.ν ξ :=
        (hν'anti (show ξ ∈ Set.Ici 0 from hx.trans hξ.1.le) (show y ∈ Set.Ici 0 from hy) hξ.2).le
      nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.2 hxy.le)]
    · simp
    · obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope E.ν hxy hνc.continuousOn
        E.ν_differentiable.differentiableOn
      rw [eq_div_iff (sub_ne_zero.2 hxy.ne')] at hd
      have : deriv E.ν ξ ≤ deriv E.ν y :=
        (hν'anti (show y ∈ Set.Ici 0 from hy) (show ξ ∈ Set.Ici 0 from hy.trans hξ.1.le) hξ.1).le
      nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.2 hxy.le)]
  have hd0 : 0 < deriv E.ν 0 := E.ν'_pos 0 le_rfl
  have hmax : ∀ θ ∈ Set.Icc θlo θhi, ∀ x, 0 ≤ x →
      E.ν x * virtualValuation D θ - E.c * x
        ≤ E.ν (m.q θ) * virtualValuation D θ - E.c * m.q θ := by
    intro θ hθ x hx
    set a := virtualValuation D θ
    by_cases h : deriv E.ν 0 * a ≤ E.c
    · rw [(hq θ hθ).1 h, E.ν_zero]
      by_cases ha : a ≤ 0
      · have := hν0 x hx
        nlinarith [E.c_pos]
      · push_neg at ha
        have h1 := htan x 0 hx le_rfl
        rw [E.ν_zero] at h1
        nlinarith [mul_le_mul_of_nonneg_right h1 ha.le, mul_le_mul_of_nonneg_right h hx]
    · push_neg at h
      have h2 := (hq θ hθ).2 h
      have ha : 0 < a := by
        by_contra ha; push_neg at ha
        nlinarith [E.c_pos]
      have h1 := htan x (m.q θ) hx (m.q_nonneg θ hθ)
      have h4 := mul_le_mul_of_nonneg_right h1 ha.le
      have h5 : (E.ν (m.q θ) + deriv E.ν (m.q θ) * (x - m.q θ)) * a
          = E.ν (m.q θ) * a + E.c * (x - m.q θ) := by
        rw [add_mul, mul_right_comm, h2]
      rw [h5] at h4
      linarith
  have hqmono : MonotoneOn m.q (Set.Icc θlo θhi) := by
    intro x hx y hy hxy
    have ha := hreg hx hy hxy
    by_cases h : deriv E.ν 0 * virtualValuation D x ≤ E.c
    · rw [(hq x hx).1 h]; exact m.q_nonneg y hy
    · push_neg at h
      have h' : E.c < deriv E.ν 0 * virtualValuation D y :=
        lt_of_lt_of_le h (mul_le_mul_of_nonneg_left ha hd0.le)
      have e1 := (hq x hx).2 h
      have e2 := (hq y hy).2 h'
      have hax : 0 < virtualValuation D x := by
        by_contra hh; push_neg at hh
        nlinarith [E.c_pos]
      by_contra hcon
      push_neg at hcon
      have hlt' : deriv E.ν (m.q x) < deriv E.ν (m.q y) :=
        hν'anti (show m.q y ∈ Set.Ici 0 from m.q_nonneg y hy)
          (show m.q x ∈ Set.Ici 0 from m.q_nonneg x hx) hcon
      have hpos : 0 < deriv E.ν (m.q y) := E.ν'_pos _ (m.q_nonneg y hy)
      nlinarith [mul_lt_mul_of_pos_right hlt' hax, mul_le_mul_of_nonneg_left ha hpos.le]
  set Q : ℝ → ℝ := fun θ => E.ν (m.q θ) with hQ
  have hQmono : MonotoneOn Q (Set.Icc θlo θhi) := fun x hx y hy hxy =>
    hνmono.monotoneOn (show m.q x ∈ Set.Ici 0 from m.q_nonneg x hx)
      (show m.q y ∈ Set.Ici 0 from m.q_nonneg y hy) (hqmono hx hy hxy)
  have hlo' : θlo ∈ Set.Icc θlo θhi := ⟨le_rfl, hab⟩
  have htlo : m.t θlo = θlo * Q θlo := by rw [ht θlo hlo']; simp [hQ]
  have ht' : ∀ θ ∈ Set.Icc θlo θhi,
      m.t θ = m.t θlo + (θ * Q θ - θlo * Q θlo) - ∫ y in θlo..θ, Q y := by
    intro θ hθ; rw [ht θ hθ, htlo]; simp only [hQ]; ring
  have hicabs : ICabs Q m.t θlo θhi := abs_ic_of_formula hab hQmono ht'
  have hIC : m.IsIC E := fun θ hθ θ' hθ' => hicabs θ hθ θ' hθ'
  have hIR : m.IsIR E := by
    intro θ hθ
    unfold QuantityMechanism.u
    rw [ht θ hθ]
    have : 0 ≤ ∫ x in θlo..θ, E.ν (m.q x) := by
      apply intervalIntegral.integral_nonneg hθ.1
      intro x hx
      exact hν0 _ (m.q_nonneg x ⟨hx.1, hx.2.trans hθ.2⟩)
    linarith
  refine ⟨hIC, hIR, ?_⟩
  intro m' hic' hir'
  obtain ⟨iJm, hpm⟩ := profit_eq D E hνmono m hIC
  obtain ⟨iJm', hpm'⟩ := profit_eq D E hνmono m' hic'
  have hδ' : 0 ≤ θlo * E.ν (m'.q θlo) - m'.t θlo := by
    have := hir' θlo hlo'; unfold QuantityMechanism.u at this; linarith
  have hδ : θlo * E.ν (m.q θlo) - m.t θlo = 0 := by rw [htlo]; simp [hQ]
  have hmono : ∫ θ in θlo..θhi, Jint D E m' θ ≤ ∫ θ in θlo..θhi, Jint D E m θ := by
    apply intervalIntegral.integral_mono_on hab iJm' iJm
    intro θ hθ
    exact mul_le_mul_of_nonneg_right (hmax θ hθ (m'.q θ) (m'.q_nonneg θ hθ)) (D.f_pos θ hθ).le
  rw [hpm', hpm, hδ]
  linarith

end MechanismDesign.Screening

open MechanismDesign.Screening


theorem solution {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (E : NonlinearEnv θhi) (hreg : IsRegular D) (m : QuantityMechanism θlo θhi)
    (hq : ∀ θ ∈ Set.Icc θlo θhi,
      (deriv E.ν 0 * virtualValuation D θ ≤ E.c → m.q θ = 0) ∧
      (E.c < deriv E.ν 0 * virtualValuation D θ →
        deriv E.ν (m.q θ) * virtualValuation D θ = E.c))
    (ht : ∀ θ ∈ Set.Icc θlo θhi, m.t θ = θ * E.ν (m.q θ) - ∫ x in θlo..θ, E.ν (m.q x)) :
    m.IsIC E ∧ m.IsIR E ∧
      ∀ m' : QuantityMechanism θlo θhi, m'.IsIC E → m'.IsIR E →
        expectedProfit D E m' ≤ expectedProfit D E m := by
  exact nonlinear_pricing_optimal_core D E hreg m hq ht
