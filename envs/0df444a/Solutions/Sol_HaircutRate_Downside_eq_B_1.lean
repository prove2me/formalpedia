-- Prove2me | solution 1 for HaircutRate.Downside.eq_B_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:45:16.63822+00:00
-- url     : https://prove2.me/submissions/04effd09-197d-4e6d-8d97-c5c2ea7500ee

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside.HLib
open Set MeasureTheory Filter Topology HaircutRate.Downside HaircutRate.Downside.Economy

variable (E : Economy)

/-- the pricing kernel. -/
noncomputable def ker (x ω : ℝ) : ℝ :=
  deriv E.u (E.e1 + E.K * min ω x) / deriv E.u (E.e1 + E.K * x) * min ω x

/-- the generalized pricing integral against a weight `g`. -/
noncomputable def Q (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ ω in E.lo..E.hi, ker E x ω * g ω

lemma qbp_eq (f : ℝ → ℝ) (x : ℝ) : E.qbp f x = Q E f x := rfl

variable {E}

lemma arg_pos (hE : E.Valid) {ω : ℝ} (hω : 0 < ω) : 0 < E.e1 + E.K * ω := by
  have := hE.e1_nonneg; have := hE.K_pos; positivity

lemma arg_pos' (hE : E.Valid) {ω : ℝ} (hω : ω ∈ Icc E.lo E.hi) : 0 < E.e1 + E.K * ω :=
  arg_pos hE (lt_of_lt_of_le hE.lo_pos hω.1)

lemma up_contDiff (hE : E.Valid) : ContDiffOn ℝ 1 (deriv E.u) (Ioi 0) :=
  hE.u_smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)

lemma up_hasDeriv (hE : E.Valid) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (deriv E.u) (deriv (deriv E.u) c) c := by
  have h := (up_contDiff hE).differentiableOn (by norm_num) c hc
  exact (h.differentiableAt (isOpen_Ioi.mem_nhds hc)).hasDerivAt

lemma up_cont (hE : E.Valid) : ContinuousOn (deriv E.u) (Ioi 0) := (up_contDiff hE).continuousOn

lemma up_anti (hE : E.Valid) : StrictAntiOn (deriv E.u) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0) (up_cont hE)
  intro x hx
  rw [interior_Ioi] at hx
  rw [(up_hasDeriv hE hx).deriv]
  exact hE.u''_neg x hx

lemma up_pos (hE : E.Valid) {ω : ℝ} (hω : ω ∈ Icc E.lo E.hi) :
    0 < deriv E.u (E.e1 + E.K * ω) := hE.u'_pos _ (arg_pos' hE hω)

/-- the two-variable kernel. -/
noncomputable def Φ (p : ℝ × ℝ) : ℝ :=
  deriv E.u (E.e1 + E.K * p.1) * p.1 / deriv E.u (E.e1 + E.K * p.2)

lemma Φ_contDiff (hE : E.Valid) :
    ContDiffOn ℝ 1 (Φ (E := E)) (Icc E.lo E.hi ×ˢ Icc E.lo E.hi) := by
  have hc : ∀ (g : ℝ × ℝ → ℝ), ContDiff ℝ 1 g →
      (∀ p ∈ Icc E.lo E.hi ×ˢ Icc E.lo E.hi, g p ∈ Icc E.lo E.hi) →
      ContDiffOn ℝ 1 (fun p => deriv E.u (E.e1 + E.K * g p)) (Icc E.lo E.hi ×ˢ Icc E.lo E.hi) := by
    intro g hg hgm
    have h1 : ContDiffOn ℝ 1 (fun p => E.e1 + E.K * g p) (Icc E.lo E.hi ×ˢ Icc E.lo E.hi) :=
      (contDiff_const.add (contDiff_const.mul hg)).contDiffOn
    exact (up_contDiff hE).comp h1 (fun p hp => arg_pos' hE (hgm p hp))
  unfold Φ
  apply ContDiffOn.div
  · exact (hc Prod.fst contDiff_fst (fun p hp => hp.1)).mul contDiff_fst.contDiffOn
  · exact hc Prod.snd contDiff_snd (fun p hp => hp.2)
  · intro p hp; exact (up_pos hE hp.2).ne'

lemma ker_eq_Φ (x ω : ℝ) : ker E x ω = Φ (E := E) (min ω x, x) := by
  unfold ker Φ; ring

lemma ker_lip (hE : E.Valid) : ∃ L : NNReal, ∀ ω ∈ Icc E.lo E.hi,
    LipschitzOnWith L (fun x => ker E x ω) (Icc E.lo E.hi) := by
  obtain ⟨L, hL⟩ := (Φ_contDiff hE).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  refine ⟨L * max 1 1, fun ω hω => ?_⟩
  have hl : LipschitzOnWith (max 1 1) (fun x : ℝ => (min ω x, x)) (Icc E.lo E.hi) :=
    ((LipschitzWith.id.const_min ω).prodMk LipschitzWith.id).lipschitzOnWith
  have := hL.comp hl (fun x hx => ⟨⟨le_min hω.1 hx.1, (min_le_right _ _).trans hx.2⟩, hx⟩)
  simpa [Function.comp_def, ker_eq_Φ] using this

lemma ker_cont (hE : E.Valid) (x : ℝ) (hx : x ∈ Icc E.lo E.hi) :
    ContinuousOn (fun ω => ker E x ω) (Icc E.lo E.hi) := by
  have : ContinuousOn (fun ω => Φ (E := E) (min ω x, x)) (Icc E.lo E.hi) := by
    apply (Φ_contDiff hE).continuousOn.comp (by fun_prop)
    intro ω hω
    exact ⟨⟨le_min hω.1 hx.1, (min_le_right _ _).trans hx.2⟩, hx⟩
  simpa [ker_eq_Φ] using this

lemma ker_int (hE : E.Valid) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume E.lo E.hi)
    {x : ℝ} (hx : x ∈ Icc E.lo E.hi) :
    IntervalIntegrable (fun ω => ker E x ω * g ω) volume E.lo E.hi := by
  apply hg.continuousOn_mul
  rw [uIcc_of_le hE.lo_lt_hi.le]
  exact ker_cont hE x hx

lemma Q_lip_bound (hE : E.Valid) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume E.lo E.hi) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ Icc E.lo E.hi, ∀ z ∈ Icc E.lo E.hi,
      |Q E g y - Q E g z| ≤ L * |y - z| := by
  obtain ⟨L, hL⟩ := ker_lip hE
  refine ⟨L * ∫ ω in E.lo..E.hi, |g ω|, ?_, fun y hy z hz => ?_⟩
  · exact mul_nonneg L.2 (intervalIntegral.integral_nonneg hE.lo_lt_hi.le (fun _ _ => abs_nonneg _))
  unfold Q
  rw [← intervalIntegral.integral_sub (ker_int hE hg hy) (ker_int hE hg hz)]
  have hb : IntervalIntegrable (fun ω => (L : ℝ) * |y - z| * |g ω|) volume E.lo E.hi :=
    hg.abs.const_mul _
  have := intervalIntegral.norm_integral_le_of_norm_le hE.lo_lt_hi.le
    (f := fun ω => ker E y ω * g ω - ker E z ω * g ω) (g := fun ω => (L : ℝ) * |y - z| * |g ω|)
    (Filter.Eventually.of_forall fun ω hω => by
      have hω' : ω ∈ Icc E.lo E.hi := Ioc_subset_Icc_self hω
      have h1 := (hL ω hω').dist_le_mul y hy z hz
      rw [Real.dist_eq, Real.dist_eq] at h1
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) hb
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]; ring

lemma Q_cont (hE : E.Valid) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume E.lo E.hi) :
    ContinuousOn (Q E g) (Icc E.lo E.hi) := by
  obtain ⟨L, hL0, hL⟩ := Q_lip_bound hE hg
  have : LipschitzOnWith (Real.toNNReal L) (Q E g) (Icc E.lo E.hi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]
    exact hL y hy z hz
  exact this.continuousOn

lemma Q_add (hE : E.Valid) {f ψ : ℝ → ℝ} (hf : IntervalIntegrable f volume E.lo E.hi)
    (hψ : IntervalIntegrable ψ volume E.lo E.hi) (τ : ℝ) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) :
    Q E (shock f ψ τ) x = Q E f x + τ * Q E ψ x := by
  unfold Q shock
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (ker_int hE hf hx)
    ((ker_int hE hψ hx).const_mul τ)]
  congr 1; funext ω; ring

/-- the a.e. partial derivative of the kernel. -/
noncomputable def kerD (E : Economy) (x ω : ℝ) : ℝ :=
  if ω ≤ x then -(deriv E.u (E.e1 + E.K * ω) * deriv (deriv E.u) (E.e1 + E.K * x)) /
      deriv E.u (E.e1 + E.K * x) ^ 2 * (E.K * ω) else 1

lemma ker_hasDeriv (hE : E.Valid) {x ω : ℝ} (hx : x ∈ Ioo E.lo E.hi) (hω : ω ∈ Icc E.lo E.hi)
    (hne : ω ≠ x) : HasDerivAt (fun y => ker E y ω) (kerD E x ω) x := by
  have hxI : x ∈ Icc E.lo E.hi := Ioo_subset_Icc_self hx
  have hpx := up_pos hE hxI
  have hlin : HasDerivAt (fun y => E.e1 + E.K * y) E.K x := by
    simpa using ((hasDerivAt_id x).const_mul E.K).const_add E.e1
  have hu : HasDerivAt (fun y => deriv E.u (E.e1 + E.K * y))
      (deriv (deriv E.u) (E.e1 + E.K * x) * E.K) x :=
    by simpa [Function.comp_def] using (up_hasDeriv hE (arg_pos' hE hxI)).comp x hlin
  rcases lt_or_gt_of_ne hne with h | h
  · -- ω < x
    have hev : (fun y => ker E y ω) =ᶠ[𝓝 x]
        (fun y => deriv E.u (E.e1 + E.K * ω) * ω * (deriv E.u (E.e1 + E.K * y))⁻¹) := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      simp only [mem_Ioi] at hy
      unfold ker; rw [min_eq_left hy.le]; ring
    have hd := (hu.inv hpx.ne').const_mul (deriv E.u (E.e1 + E.K * ω) * ω)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    unfold kerD; rw [if_pos h.le]; field_simp
  · -- ω > x
    have hev : (fun y => ker E y ω) =ᶠ[𝓝 x] (fun y => y) := by
      have hc : ContinuousAt (fun y => deriv E.u (E.e1 + E.K * y)) x := hu.continuousAt
      filter_upwards [Iio_mem_nhds h, hc.eventually (lt_mem_nhds hpx)] with y hy hy2
      simp only [mem_Iio] at hy
      unfold ker; rw [min_eq_right hy.le]; field_simp
    refine ((hasDerivAt_id x).congr_of_eventuallyEq hev).congr_deriv ?_
    unfold kerD; rw [if_neg (not_le.mpr h)]

lemma kerD_meas (x : ℝ) : Measurable (kerD E x) := by
  unfold kerD
  refine Measurable.ite measurableSet_Iic ?_ measurable_const
  have h1 : Measurable (fun ω => deriv E.u (E.e1 + E.K * ω)) :=
    (measurable_deriv _).comp (by fun_prop)
  fun_prop

lemma cdf_split {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) :
    ∫ ω in x..E.hi, f ω = 1 - E.cdf f x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.integrable.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le (hx.1.trans hx.2)]; exact Icc_subset_Icc le_rfl hx.2))
    (hf.integrable.mono_set (by rw [uIcc_of_le hx.2, uIcc_of_le (hx.1.trans hx.2)]; exact Icc_subset_Icc hx.1 le_rfl))
  rw [hf.total] at h1; unfold cdf; linarith

lemma cdf_nonneg {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) :
    0 ≤ E.cdf f x :=
  intervalIntegral.integral_nonneg hx.1 (fun ω hω => hf.nonneg ω ⟨hω.1, hω.2.trans hx.2⟩)

lemma cdf_le_one {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) :
    E.cdf f x ≤ 1 := by
  have := cdf_split hf hx
  have h2 : 0 ≤ ∫ ω in x..E.hi, f ω :=
    intervalIntegral.integral_nonneg hx.2 (fun ω hω => hf.nonneg ω ⟨hx.1.trans hω.1, hω.2⟩)
  linarith

theorem eqB1 (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    ∀ x ∈ Ioo E.lo E.hi, HasDerivAt (E.qbp f) (E.dqbp f x) x ∧ 0 < E.dqbp f x := by
  intro x hx
  have hxI : x ∈ Icc E.lo E.hi := Ioo_subset_Icc_self hx
  have hlh := hE.lo_lt_hi.le
  obtain ⟨L, hL⟩ := ker_lip hE
  have hfI := hf.integrable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun y ω => ker E y ω * f ω) (F' := fun ω => kerD E x ω * f ω)
    (bound := fun ω => (L : ℝ) * |f ω|) (x₀ := x) (s := Ioo E.lo E.hi)
    (isOpen_Ioo.mem_nhds hx)
    (by filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact (ker_int hE hfI (Ioo_subset_Icc_self hy)).def'.aestronglyMeasurable)
    (ker_int hE hfI hxI)
    ((kerD_meas x).aestronglyMeasurable.mul hfI.def'.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω hω => by
      rw [uIoc_of_le hlh] at hω
      have hω' : ω ∈ Icc E.lo E.hi := Ioc_subset_Icc_self hω
      apply LipschitzOnWith.of_dist_le_mul
      intro y hy z hz
      have h1 := (hL ω hω').dist_le_mul y (Ioo_subset_Icc_self hy) z (Ioo_subset_Icc_self hz)
      rw [Real.dist_eq] at h1 ⊢
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity : (0:ℝ) ≤ L * |f ω|), ← sub_mul, abs_mul]
      calc |ker E y ω - ker E z ω| * |f ω| ≤ (L * dist y z) * |f ω| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = _ := by ring)
    (hfI.abs.const_mul _)
    (by
      filter_upwards [Measure.ae_ne volume x] with ω hne hω
      rw [uIoc_of_le hlh] at hω
      exact (ker_hasDeriv hE hx (Ioc_subset_Icc_self hω) hne).mul_const _)
  obtain ⟨hint, hder⟩ := key
  have hval : (∫ ω in E.lo..E.hi, kerD E x ω * f ω) = E.dqbp f x := by
    have hi1 : IntervalIntegrable (fun ω => kerD E x ω * f ω) volume E.lo x :=
      hint.mono_set (by rw [uIcc_of_le hlh, uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le)
    have hi2 : IntervalIntegrable (fun ω => kerD E x ω * f ω) volume x E.hi :=
      hint.mono_set (by rw [uIcc_of_le hlh, uIcc_of_le hx.2.le]; exact Icc_subset_Icc hx.1.le le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    unfold dqbp
    rw [← cdf_split hf hxI]
    congr 1
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with ω hω
      rw [uIoc_of_le hx.1.le] at hω
      unfold kerD; rw [if_pos hω.2]
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with ω hω
      rw [uIoc_of_le hx.2.le] at hω
      unfold kerD; rw [if_neg (not_le.mpr hω.1)]; ring
  refine ⟨by rw [← hval]; exact hder, ?_⟩
  -- positivity
  have hpx := up_pos hE hxI
  have hb := hE.u''_neg _ (arg_pos' hE hxI)
  set m := -(deriv (deriv E.u) (E.e1 + E.K * x)) / deriv E.u (E.e1 + E.K * x) * (E.K * E.lo)
    with hm
  have hm0 : 0 < m := by
    have := hE.K_pos; have := hE.lo_pos
    rw [hm]; exact mul_pos (div_pos (neg_pos.mpr hb) hpx) (mul_pos hE.K_pos hE.lo_pos)
  have hfx : IntervalIntegrable f volume E.lo x :=
    hfI.mono_set (by rw [uIcc_of_le hlh, uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le)
  have hcont : ContinuousOn (fun ω => -(deriv E.u (E.e1 + E.K * ω) *
      deriv (deriv E.u) (E.e1 + E.K * x)) / deriv E.u (E.e1 + E.K * x) ^ 2 * (E.K * ω))
      (uIcc E.lo x) := by
    rw [uIcc_of_le hx.1.le]
    have : ContinuousOn (fun ω => deriv E.u (E.e1 + E.K * ω)) (Icc E.lo x) :=
      (up_cont hE).comp (by fun_prop) (fun ω hω => arg_pos' hE ⟨hω.1, hω.2.trans hx.2.le⟩)
    exact ((this.mul continuousOn_const).neg.div continuousOn_const
      (fun _ _ => (pow_pos hpx 2).ne')).mul (continuousOn_const.mul continuousOn_id)
  have hlow : m * E.cdf f x ≤ ∫ ω in E.lo..x, -(deriv E.u (E.e1 + E.K * ω) *
      deriv (deriv E.u) (E.e1 + E.K * x)) / deriv E.u (E.e1 + E.K * x) ^ 2 * (E.K * ω) * f ω := by
    unfold cdf
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hx.1.le (hfx.const_mul m) (hfx.continuousOn_mul hcont)
    intro ω hω
    have hωI : ω ∈ Icc E.lo E.hi := ⟨hω.1, hω.2.trans hx.2.le⟩
    have hfω := hf.nonneg ω hωI
    apply mul_le_mul_of_nonneg_right _ hfω
    have hpω := up_pos hE hωI
    have hmono : deriv E.u (E.e1 + E.K * x) ≤ deriv E.u (E.e1 + E.K * ω) := by
      rcases eq_or_lt_of_le hω.2 with h | h
      · rw [h]
      · exact ((up_anti hE) (arg_pos' hE hωI) (arg_pos' hE hxI)
          (by have := hE.K_pos; nlinarith)).le
    rw [hm]
    have hK := hE.K_pos
    have hnb : 0 < -deriv (deriv E.u) (E.e1 + E.K * x) := neg_pos.mpr hb
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hpx (pow_pos hpx 2)]
    have e1 : -(deriv E.u (E.e1 + E.K * ω) * deriv (deriv E.u) (E.e1 + E.K * x)) * (E.K * ω)
        = (-deriv (deriv E.u) (E.e1 + E.K * x)) * deriv E.u (E.e1 + E.K * ω) * (E.K * ω) := by ring
    rw [e1]
    have : (-deriv (deriv E.u) (E.e1 + E.K * x)) * (E.K * E.lo) * deriv E.u (E.e1 + E.K * x) ^ 2
        ≤ (-deriv (deriv E.u) (E.e1 + E.K * x)) * deriv E.u (E.e1 + E.K * ω) * (E.K * ω) *
          deriv E.u (E.e1 + E.K * x) := by
      have h3 : E.K * E.lo ≤ E.K * ω := by nlinarith [hω.1]
      have h4 : deriv E.u (E.e1 + E.K * x) * (E.K * E.lo) ≤ deriv E.u (E.e1 + E.K * ω) * (E.K * ω) :=
        mul_le_mul hmono h3 (mul_pos hK hE.lo_pos).le hpω.le
      nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hnb.le hpx.le)]
    linarith
  unfold dqbp
  have h0 := cdf_nonneg hf hxI
  have h1 := cdf_le_one hf hxI
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h] at hlow ⊢; linarith
  · nlinarith

end HaircutRate.Downside.HLib

open Set HaircutRate.Downside HaircutRate.Downside.Economy

theorem solution (E : Economy) (hE : E.Valid) (f : ℝ → ℝ) (hf : E.IsDensity f) :
    ∀ x ∈ Ioo E.lo E.hi, HasDerivAt (E.qbp f) (E.dqbp f x) x ∧ 0 < E.dqbp f x :=
  HLib.eqB1 hE hf
