-- Prove2me | solution 1 for HaircutRate.Downside.eq_35
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:58:53.746985+00:00
-- url     : https://prove2.me/submissions/1e47fe6b-f1d1-47e1-b185-2f201494f50f

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

lemma qbp_cont (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    ContinuousOn (E.qbp f) (Icc E.lo E.hi) := Q_cont hE hf.integrable

theorem lemma1 (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    StrictMonoOn (E.qbp f) (Icc E.lo E.hi) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (qbp_cont hE hf)
  intro x hx
  rw [interior_Icc] at hx
  rw [((eqB1 hE hf) x hx).1.deriv]
  exact ((eqB1 hE hf) x hx).2

lemma up_le (hE : E.Valid) {a b : ℝ} (ha : a ∈ Icc E.lo E.hi) (hb : b ∈ Icc E.lo E.hi)
    (hab : a ≤ b) : deriv E.u (E.e1 + E.K * b) ≤ deriv E.u (E.e1 + E.K * a) := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact ((up_anti hE) (arg_pos' hE ha) (arg_pos' hE hb) (by have := hE.K_pos; nlinarith)).le

lemma ker_ge (hE : E.Valid) {x ω : ℝ} (hx : x ∈ Icc E.lo E.hi) (hω : ω ∈ Icc E.lo E.hi) :
    E.lo ≤ ker E x ω := by
  have hm : min ω x ∈ Icc E.lo E.hi := ⟨le_min hω.1 hx.1, (min_le_right _ _).trans hx.2⟩
  have h1 := up_le hE hm hx (min_le_right _ _)
  have hpx := up_pos hE hx
  have hr : 1 ≤ deriv E.u (E.e1 + E.K * min ω x) / deriv E.u (E.e1 + E.K * x) := by
    rw [le_div_iff₀ hpx]; linarith
  unfold ker
  have : E.lo ≤ min ω x := hm.1
  have hlo := hE.lo_pos
  nlinarith

lemma qbp_ge (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) :
    E.lo ≤ E.qbp f x := by
  have : (∫ ω in E.lo..E.hi, E.lo * f ω) ≤ E.qbp f x := by
    apply intervalIntegral.integral_mono_on hE.lo_lt_hi.le (hf.integrable.const_mul _)
      (ker_int hE hf.integrable hx)
    intro ω hω
    exact mul_le_mul_of_nonneg_right (ker_ge hE hx hω) (hf.nonneg ω hω)
  rw [intervalIntegral.integral_const_mul, hf.total, mul_one] at this
  exact this

lemma qbp_lo (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) : E.qbp f E.lo = E.lo := by
  have : E.qbp f E.lo = ∫ ω in E.lo..E.hi, E.lo * f ω := by
    rw [qbp_eq]; unfold Q
    apply intervalIntegral.integral_congr
    intro ω hω
    rw [uIcc_of_le hE.lo_lt_hi.le] at hω
    dsimp only; unfold ker
    rw [min_eq_right hω.1, div_self (up_pos hE ⟨le_rfl, hE.lo_lt_hi.le⟩).ne', one_mul]
  rw [this, intervalIntegral.integral_const_mul, hf.total, mul_one]

lemma qbp_hi (hE : E.Valid) (f : ℝ → ℝ) : E.qbp f E.hi =
    E.expect f (fun ω => deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * E.hi) * ω) := by
  rw [qbp_eq]; unfold Q expect
  apply intervalIntegral.integral_congr
  intro ω hω
  rw [uIcc_of_le hE.lo_lt_hi.le] at hω
  dsimp only; unfold ker
  rw [min_eq_left hω.2]

lemma G_strictMono (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    StrictMonoOn (fun x => x + E.qbp f x) (Icc E.lo E.hi) := by
  intro a ha b hb hab
  have := lemma1 hE hf ha hb hab
  simp only; linarith

theorem theorem1 (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) (hA2 : E.Assumption2 f) :
    (∃! x, E.IsFaceValue f x) ∧ E.IsFaceValue f (E.faceValue f) ∧
      E.faceValue f ∈ Ioo E.lo E.hi := by
  have hlh := hE.lo_lt_hi.le
  have hcont : ContinuousOn (fun x => x + E.qbp f x) (Icc E.lo E.hi) :=
    continuousOn_id.add (qbp_cont hE hf)
  have hmem : E.D ∈ Ioo ((fun x => x + E.qbp f x) E.lo) ((fun x => x + E.qbp f x) E.hi) := by
    simp only [qbp_lo hE hf, qbp_hi hE f]
    exact ⟨by linarith [hA2.1], hA2.2⟩
  obtain ⟨x0, hx0, hx0D⟩ := intermediate_value_Ioo hlh hcont hmem
  have hroot : E.IsFaceValue f x0 := ⟨Ioo_subset_Icc_self hx0, hx0D⟩
  have huniq : ∀ y, E.IsFaceValue f y → y = x0 := by
    intro y hy
    exact (G_strictMono hE hf).injOn hy.1 hroot.1 (by rw [hy.2]; exact hx0D.symm)
  have hex : ∃ x, E.IsFaceValue f x := ⟨x0, hroot⟩
  have hfv : E.IsFaceValue f (E.faceValue f) := by
    unfold faceValue; rw [dif_pos hex]; exact hex.choose_spec
  refine ⟨⟨x0, hroot, huniq⟩, hfv, ?_⟩
  rw [huniq _ hfv]; exact hx0

theorem marginal (hE : E.Valid) (hA3 : E.Assumption3) :
    StrictMonoOn (fun c => deriv E.u (E.e1 + c) * c) (Icc (E.K * E.lo) (E.K * E.hi)) ∧
      StrictMonoOn (fun ω => deriv E.u (E.e1 + E.K * ω) * ω) (Icc E.lo E.hi) := by
  have hK := hE.K_pos
  have hKlo : 0 < E.K * E.lo := mul_pos hK hE.lo_pos
  have hpos : ∀ c ∈ Icc (E.K * E.lo) (E.K * E.hi), 0 < E.e1 + c := fun c hc => by
    have := hE.e1_nonneg; linarith [hc.1]
  have h1 : StrictMonoOn (fun c => deriv E.u (E.e1 + c) * c) (Icc (E.K * E.lo) (E.K * E.hi)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · apply ContinuousOn.mul _ continuousOn_id
      exact (up_cont hE).comp (by fun_prop) (fun c hc => hpos c hc)
    · intro c hc
      rw [interior_Icc] at hc
      have hcI := Ioo_subset_Icc_self hc
      have hd : HasDerivAt (fun c => deriv E.u (E.e1 + c) * c)
          (deriv (deriv E.u) (E.e1 + c) * c + deriv E.u (E.e1 + c)) c := by
        have h0 : HasDerivAt (fun c => deriv E.u (E.e1 + c)) (deriv (deriv E.u) (E.e1 + c)) c := by
          have := (up_hasDeriv hE (hpos c hcI)).comp c ((hasDerivAt_id c).const_add E.e1)
          simpa [Function.comp_def] using this
        exact (h0.mul (hasDerivAt_id' c)).congr_deriv (by ring)
      rw [hd.deriv]
      have hA := hA3 c hcI
      have hp := hE.u'_pos _ (hpos c hcI)
      rw [div_lt_one hp] at hA
      linarith
  refine ⟨h1, ?_⟩
  intro a ha b hb hab
  have ha' : E.K * a ∈ Icc (E.K * E.lo) (E.K * E.hi) :=
    ⟨by nlinarith [ha.1], by nlinarith [ha.2]⟩
  have hb' : E.K * b ∈ Icc (E.K * E.lo) (E.K * E.hi) :=
    ⟨by nlinarith [hb.1], by nlinarith [hb.2]⟩
  have := h1 ha' hb' (by nlinarith)
  simp only at this ⊢
  have e : ∀ t, deriv E.u (E.e1 + E.K * t) * t = deriv E.u (E.e1 + E.K * t) * (E.K * t) / E.K :=
    fun t => by field_simp
  rw [e a, e b]
  exact div_lt_div_of_pos_right this hK

lemma int_zero_ae {a b : ℝ} {g : ℝ → ℝ} (h : ∀ᵐ ω ∂volume, ω ∈ uIoc a b → g ω = 0) :
    ∫ ω in a..b, g ω = 0 := by
  rw [intervalIntegral.integral_congr_ae h]; simp

lemma int_zero_on {a b : ℝ} {g : ℝ → ℝ} (h : EqOn g (fun _ => 0) (uIcc a b)) :
    ∫ ω in a..b, g ω = 0 := by
  rw [intervalIntegral.integral_congr h]; simp

lemma sub_int {g : ℝ → ℝ} (hE : E.Valid) (hg : IntervalIntegrable g volume E.lo E.hi) {a b : ℝ}
    (ha : a ∈ Icc E.lo E.hi) (hb : b ∈ Icc E.lo E.hi) : IntervalIntegrable g volume a b := by
  apply hg.mono_set
  rw [uIcc_of_le hE.lo_lt_hi.le]
  exact uIcc_subset_Icc ha hb

lemma psi_split (hE : E.Valid) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) {ψ : ℝ → ℝ}
    (hψ : E.IsDownsideImprovement x ψ) (v : ℝ → ℝ)
    (hint : IntervalIntegrable (fun ω => v ω * ψ ω) volume E.lo E.hi) :
    ∫ ω in E.lo..E.hi, v ω * ψ ω = ∫ ω in E.lo..x, v ω * ψ ω := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (sub_int hE hint ⟨le_rfl, hE.lo_lt_hi.le⟩ hx) (sub_int hE hint hx ⟨hE.lo_lt_hi.le, le_rfl⟩)]
  have : ∫ ω in x..E.hi, v ω * ψ ω = 0 := by
    apply int_zero_ae
    filter_upwards with ω hω
    rw [uIoc_of_le hx.2] at hω
    rw [hψ.support ω (fun h => absurd h.2 (not_lt.mpr hω.1.le)), mul_zero]
  rw [this, add_zero]

lemma psi_total (hE : E.Valid) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) {ψ : ℝ → ℝ}
    (hψ : E.IsDownsideImprovement x ψ) : ∫ ω in E.lo..E.hi, ψ ω = 0 := by
  have := psi_split hE hx hψ (fun _ => 1) (by simpa using hψ.integrable)
  simp only [one_mul] at this
  rw [this, hψ.mass]

lemma Qpsi_eq (hE : E.Valid) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) {ψ : ℝ → ℝ}
    (hψ : E.IsDownsideImprovement x ψ) {y : ℝ} (hy : y ∈ Icc x E.hi) :
    Q E ψ y = ∫ ω in E.lo..x, deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * y) * ω * ψ ω := by
  have hyI : y ∈ Icc E.lo E.hi := ⟨hx.1.trans hy.1, hy.2⟩
  unfold Q
  rw [psi_split hE hx hψ (fun ω => ker E y ω) (ker_int hE hψ.integrable hyI)]
  apply intervalIntegral.integral_congr
  intro ω hω
  rw [uIcc_of_le hx.1] at hω
  dsimp only; unfold ker; rw [min_eq_left (hω.2.trans hy.1)]

lemma Qpsi_pos (hE : E.Valid) (hA3 : E.Assumption3) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) {ψ : ℝ → ℝ}
    (hψ : E.IsDownsideImprovement x ψ) {y : ℝ} (hy : y ∈ Icc x E.hi) : 0 < Q E ψ y := by
  have hyI : y ∈ Icc E.lo E.hi := ⟨hx.1.trans hy.1, hy.2⟩
  rw [Qpsi_eq hE hx hψ hy]
  apply hψ.fosd
  intro a ha b hb hab
  have hm := (marginal hE hA3).2 ⟨ha.1, ha.2.trans hx.2⟩ ⟨hb.1, hb.2.trans hx.2⟩ hab
  simp only at hm ⊢
  have hp := up_pos hE hyI
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact div_lt_div_of_pos_right hm hp

theorem footnote26 (hE : E.Valid) (hA3 : E.Assumption3) {f : ℝ → ℝ} (hf : E.IsDensity f)
    (hA2 : E.Assumption2 f) {ψ : ℝ → ℝ} (hψ : E.IsDownsideImprovement (E.faceValue f) ψ) :
    HasDerivAt (fun τ => E.qbp (shock f ψ τ) (E.faceValue f)) (E.dqTau ψ (E.faceValue f)) 0 ∧
      0 < E.dqTau ψ (E.faceValue f) := by
  have hx := Ioo_subset_Icc_self (theorem1 hE hf hA2).2.2
  have hQ : Q E ψ (E.faceValue f) = E.dqTau ψ (E.faceValue f) :=
    Qpsi_eq hE hx hψ ⟨le_rfl, hx.2⟩
  refine ⟨?_, hQ ▸ Qpsi_pos hE hA3 hx hψ ⟨le_rfl, hx.2⟩⟩
  have : (fun τ => E.qbp (shock f ψ τ) (E.faceValue f)) =
      fun τ => Q E f (E.faceValue f) + τ * Q E ψ (E.faceValue f) := by
    funext τ; rw [qbp_eq, Q_add hE hf.integrable hψ.integrable τ hx]
  rw [this, ← hQ]
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (Q E ψ (E.faceValue f))).const_add
    (Q E f (E.faceValue f))

/-! ### equity -/

lemma maxk_int (hE : E.Valid) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume E.lo E.hi) (y : ℝ) :
    IntervalIntegrable (fun ω => max (ω - y) 0 * g ω) volume E.lo E.hi :=
  hg.continuousOn_mul (by fun_prop)

/-- equity integral against a general weight. -/
noncomputable def Eqty (E : Economy) (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ ω in E.lo..E.hi, max (ω - y) 0 * g ω

lemma equity_eq (f : ℝ → ℝ) (y : ℝ) : E.equity f y = Eqty E f y := rfl

lemma Eq_add (hE : E.Valid) {f ψ : ℝ → ℝ} (hf : IntervalIntegrable f volume E.lo E.hi)
    (hψ : IntervalIntegrable ψ volume E.lo E.hi) (τ y : ℝ) :
    Eqty E (shock f ψ τ) y = Eqty E f y + τ * Eqty E ψ y := by
  unfold Eqty shock
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (maxk_int hE hf y)
    ((maxk_int hE hψ y).const_mul τ)]
  congr 1; funext ω; ring

lemma Eq_cont (hE : E.Valid) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume E.lo E.hi) :
    Continuous (Eqty E g) := by
  have : LipschitzWith (Real.toNNReal (∫ ω in E.lo..E.hi, |g ω|)) (Eqty E g) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _
      (intervalIntegral.integral_nonneg hE.lo_lt_hi.le (fun _ _ => abs_nonneg _))]
    unfold Eqty
    rw [← intervalIntegral.integral_sub (maxk_int hE hg y) (maxk_int hE hg z)]
    have := intervalIntegral.norm_integral_le_of_norm_le hE.lo_lt_hi.le
      (f := fun ω => max (ω - y) 0 * g ω - max (ω - z) 0 * g ω)
      (g := fun ω => |y - z| * |g ω|)
      (Filter.Eventually.of_forall fun ω _ => by
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [abs_le]; constructor <;>
          rcases le_total (ω - y) 0 with h1 | h1 <;> rcases le_total (ω - z) 0 with h2 | h2 <;>
          simp only [max_eq_left, max_eq_right, h1, h2] <;>
          cases abs_cases (y - z) <;> linarith)
      (hg.abs.const_mul _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at this
    linarith
  exact this.continuous

lemma Eq_psi_zero (hE : E.Valid) {x : ℝ} {ψ : ℝ → ℝ} (hψ : E.IsDownsideImprovement x ψ) :
    Eqty E ψ x = 0 := by
  unfold Eqty
  apply int_zero_on
  intro ω _
  dsimp only
  rcases le_or_gt ω x with h | h
  · rw [max_eq_right (by linarith), zero_mul]
  · rw [hψ.support ω (fun h' => absurd h'.2 (not_lt.mpr h.le)), mul_zero]

lemma Eq_psi_nonneg (hE : E.Valid) {x : ℝ} (hx : x ∈ Icc E.lo E.hi) {ψ : ℝ → ℝ}
    (hψ : E.IsDownsideImprovement x ψ) (y : ℝ) : 0 ≤ Eqty E ψ y := by
  unfold Eqty
  rw [psi_split hE hx hψ (fun ω => max (ω - y) 0) (maxk_int hE hψ.integrable y)]
  set A := ∫ ω in E.lo..x, max (ω - y) 0 * ψ ω
  set B := ∫ ω in E.lo..x, ω * ψ ω
  have hψx : IntervalIntegrable ψ volume E.lo x := sub_int hE hψ.integrable ⟨le_rfl, hE.lo_lt_hi.le⟩ hx
  have key : ∀ ε > 0, 0 < A + ε * B := by
    intro ε hε
    have h := hψ.fosd (fun ω => max (ω - y) 0 + ε * ω) (by
      intro a _ b _ hab
      simp only
      have : max (a - y) 0 ≤ max (b - y) 0 := max_le_max (by linarith) le_rfl
      nlinarith)
    have e : (∫ ω in E.lo..x, (max (ω - y) 0 + ε * ω) * ψ ω) = A + ε * B := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (hψx.continuousOn_mul (by fun_prop)) ((hψx.continuousOn_mul (by fun_prop)).const_mul ε)]
      congr 1; funext ω; ring
    linarith
  by_contra hA
  push Not at hA
  have h1 := key (-A / (2 * (|B| + 1))) (div_pos (by linarith) (by positivity))
  have h2 : -A / (2 * (|B| + 1)) * B ≤ -A / (2 * (|B| + 1)) * |B| :=
    mul_le_mul_of_nonneg_left (le_abs_self B) (div_pos (by linarith) (by positivity)).le
  have h3 : -A / (2 * (|B| + 1)) * |B| ≤ -A / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg B]
  linarith

lemma equity_hasDeriv (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ}
    (hx : x ∈ Ioo E.lo E.hi) : HasDerivAt (E.equity f) (-(1 - E.cdf f x)) x := by
  have hxI : x ∈ Icc E.lo E.hi := Ioo_subset_Icc_self hx
  have hlh := hE.lo_lt_hi.le
  have hfI := hf.integrable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun y ω => max (ω - y) 0 * f ω) (F' := fun ω => (if x < ω then (-1:ℝ) else 0) * f ω)
    (bound := fun ω => |f ω|) (x₀ := x) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => (maxk_int hE hfI y).def'.aestronglyMeasurable)
    (maxk_int hE hfI x)
    ((Measurable.ite measurableSet_Ioi measurable_const measurable_const).aestronglyMeasurable.mul
      hfI.def'.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω _ => by
      apply LipschitzOnWith.of_dist_le_mul
      intro y _ z _
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_abs, ← sub_mul, abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]; constructor <;>
        rcases le_total (ω - y) 0 with h1 | h1 <;> rcases le_total (ω - z) 0 with h2 | h2 <;>
        simp only [max_eq_left, max_eq_right, h1, h2] <;>
        cases abs_cases (y - z) <;> linarith)
    hfI.abs
    (by
      filter_upwards [Measure.ae_ne volume x] with ω hne _
      rcases lt_or_gt_of_ne hne with h | h
      · have hev : (fun y => max (ω - y) 0 * f ω) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [Ioi_mem_nhds h] with y hy
          simp only [mem_Ioi] at hy
          rw [max_eq_right (by linarith), zero_mul]
        rw [if_neg (not_lt.mpr h.le), zero_mul]
        exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev
      · have hev : (fun y => max (ω - y) 0 * f ω) =ᶠ[𝓝 x] fun y => (ω - y) * f ω := by
          filter_upwards [Iio_mem_nhds h] with y hy
          simp only [mem_Iio] at hy
          rw [max_eq_left (by linarith)]
        rw [if_pos h]
        refine HasDerivAt.congr_of_eventuallyEq ?_ hev
        simpa using ((hasDerivAt_id x).const_sub ω).mul_const (f ω))
  obtain ⟨hint, hder⟩ := key
  have hval : (∫ ω in E.lo..E.hi, (if x < ω then (-1:ℝ) else 0) * f ω) = -(1 - E.cdf f x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (sub_int hE hint ⟨le_rfl, hlh⟩ hxI)
      (sub_int hE hint hxI ⟨hlh, le_rfl⟩), ← cdf_split hf hxI]
    have h1 : (∫ ω in E.lo..x, (if x < ω then (-1:ℝ) else 0) * f ω) = 0 := by
      apply int_zero_ae
      filter_upwards with ω hω
      rw [uIoc_of_le hxI.1] at hω
      rw [if_neg (not_lt.mpr hω.2), zero_mul]
    have h2 : (∫ ω in x..E.hi, (if x < ω then (-1:ℝ) else 0) * f ω) = ∫ ω in x..E.hi, -f ω := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with ω hω
      rw [uIoc_of_le hxI.2] at hω
      rw [if_pos hω.1]; ring
    rw [h1, h2, intervalIntegral.integral_neg, zero_add]
  rw [← hval]; exact hder

lemma equity_split (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ}
    (hx : x ∈ Icc E.lo E.hi) :
    E.equity f x = (∫ ω in x..E.hi, ω * f ω) - x * (1 - E.cdf f x) := by
  have hlh := hE.lo_lt_hi.le
  have hint := maxk_int hE hf.integrable x
  rw [equity_eq]; unfold Eqty
  rw [← intervalIntegral.integral_add_adjacent_intervals (sub_int hE hint ⟨le_rfl, hlh⟩ hx)
    (sub_int hE hint hx ⟨hlh, le_rfl⟩), ← cdf_split hf hx]
  have h1 : (∫ ω in E.lo..x, max (ω - x) 0 * f ω) = 0 := by
    apply int_zero_on
    intro ω hω
    rw [uIcc_of_le hx.1] at hω
    dsimp only; rw [max_eq_right (by linarith [hω.2]), zero_mul]
  have hfx : IntervalIntegrable f volume x E.hi := sub_int hE hf.integrable hx ⟨hlh, le_rfl⟩
  have h2 : (∫ ω in x..E.hi, max (ω - x) 0 * f ω) = ∫ ω in x..E.hi, (ω * f ω - x * f ω) := by
    apply intervalIntegral.integral_congr
    intro ω hω
    rw [uIcc_of_le hx.2] at hω
    dsimp only; rw [max_eq_left (by linarith [hω.1])]; ring
  have hfx1 : IntervalIntegrable (fun ω => ω * f ω) volume x E.hi :=
    hfx.continuousOn_mul continuousOn_id
  rw [h1, h2, intervalIntegral.integral_sub hfx1 (hfx.const_mul x),
    intervalIntegral.integral_const_mul]
  ring

lemma D_sub_pos (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ}
    (hfv : E.IsFaceValue f x) : 0 < E.D - x := by
  have := qbp_ge hE hf hfv.1; have := hfv.2; have := hE.lo_pos; linarith

lemma Phi_hasDeriv (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) {x : ℝ}
    (hx : x ∈ Ioo E.lo E.hi) (hxD : x < E.D) :
    HasDerivAt (fun y => E.equity f y / (E.D - y)) (E.margin f x / (E.D - x) ^ 2) x := by
  have hxI : x ∈ Icc E.lo E.hi := Ioo_subset_Icc_self hx
  have hne : E.D - x ≠ 0 := by linarith
  have h := (equity_hasDeriv hE hf hx).div ((hasDerivAt_id x).const_sub E.D) hne
  refine h.congr_deriv ?_
  unfold margin
  rw [equity_split hE hf hxI]
  simp only [id]
  ring

theorem eqB6B8 (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) (hA2 : E.Assumption2 f) :
    E.equity f (E.faceValue f) / E.bondPrice f =
        E.equity f (E.faceValue f) / (E.D - E.faceValue f) ∧
      ∀ x ∈ Ioo E.lo E.hi, x < E.D →
        HasDerivAt (fun y => E.equity f y / (E.D - y)) (E.margin f x / (E.D - x) ^ 2) x ∧
          (0 < E.margin f x / (E.D - x) ^ 2 ↔
            (1 - E.cdf f x) * E.D < ∫ ω in x..E.hi, ω * f ω) := by
  refine ⟨?_, fun x hx hxD => ⟨Phi_hasDeriv hE hf hx hxD, ?_⟩⟩
  · have := (theorem1 hE hf hA2).2.1.2
    unfold bondPrice
    congr 1; linarith
  · have : 0 < (E.D - x) ^ 2 := by have : 0 < E.D - x := by linarith
                                   positivity
    rw [div_pos_iff_of_pos_right this]
    unfold margin
    constructor <;> intro h <;> linarith

/-! ### Lemma 2 and Lemma 3 -/

lemma equity_anti (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    AntitoneOn (E.equity f) (Icc E.lo E.hi) := by
  intro x _ y _ hxy
  apply intervalIntegral.integral_mono_on hE.lo_lt_hi.le (maxk_int hE hf.integrable y)
    (maxk_int hE hf.integrable x)
  intro ω hω
  exact mul_le_mul_of_nonneg_right (max_le_max (by linarith) le_rfl) (hf.nonneg ω hω)

lemma equity_nonneg {f : ℝ → ℝ} (hE : E.Valid) (hf : E.IsDensity f) (y : ℝ) :
    0 ≤ E.equity f y :=
  intervalIntegral.integral_nonneg hE.lo_lt_hi.le
    (fun ω hω => mul_nonneg (le_max_right _ _) (hf.nonneg ω hω))

lemma ker_ratio_ge (hE : E.Valid) {y ω : ℝ} (hy : y ∈ Icc E.lo E.hi) (hω : ω ∈ Icc E.lo E.hi)
    (h : ω ≤ y) : ω ≤ ker E y ω := by
  unfold ker
  rw [min_eq_left h]
  have h1 := up_le hE hω hy h
  have hpy := up_pos hE hy
  have hr : 1 ≤ deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * y) := by
    rw [le_div_iff₀ hpy]; linarith
  have := hE.lo_pos
  nlinarith [hω.1]

theorem lemma2 (hE : E.Valid) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    AntitoneOn (E.equity f) (Icc E.lo E.hi) ∧
      MonotoneOn (fun x => E.qbp f x + E.equity f x) (Icc E.lo E.hi) ∧
      AntitoneOn (fun x => E.equity f x / (E.qbp f x + E.equity f x)) (Icc E.lo E.hi) := by
  have hmono : MonotoneOn (fun x => E.qbp f x + E.equity f x) (Icc E.lo E.hi) := by
    intro x hx y hy hxy
    simp only
    rw [qbp_eq, qbp_eq, equity_eq, equity_eq]; unfold Q Eqty
    rw [← intervalIntegral.integral_add (ker_int hE hf.integrable hx) (maxk_int hE hf.integrable x),
      ← intervalIntegral.integral_add (ker_int hE hf.integrable hy) (maxk_int hE hf.integrable y)]
    apply intervalIntegral.integral_mono_on hE.lo_lt_hi.le
      ((ker_int hE hf.integrable hx).add (maxk_int hE hf.integrable x))
      ((ker_int hE hf.integrable hy).add (maxk_int hE hf.integrable y))
    intro ω hω
    rw [← add_mul, ← add_mul]
    apply mul_le_mul_of_nonneg_right _ (hf.nonneg ω hω)
    rcases le_or_gt ω x with h1 | h1
    · -- ω ≤ x ≤ y
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      unfold ker
      rw [min_eq_left h1, min_eq_left (h1.trans hxy)]
      have hle := up_le hE hx hy hxy
      have hpx := up_pos hE hx
      have hpy := up_pos hE hy
      have hpw := up_pos hE hω
      have : deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * x) ≤
          deriv E.u (E.e1 + E.K * ω) / deriv E.u (E.e1 + E.K * y) :=
        div_le_div_of_nonneg_left hpw.le hpy hle
      have hw0 : 0 ≤ ω := by linarith [hE.lo_pos, hω.1]
      nlinarith
    · rcases le_or_gt ω y with h2 | h2
      · -- x < ω ≤ y
        rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        have := ker_ratio_ge hE hy hω h2
        have hkx : ker E x ω = x := by
          unfold ker; rw [min_eq_right h1.le, div_self (up_pos hE hx).ne', one_mul]
        rw [hkx]; linarith
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        have hkx : ker E x ω = x := by
          unfold ker; rw [min_eq_right h1.le, div_self (up_pos hE hx).ne', one_mul]
        have hky : ker E y ω = y := by
          unfold ker; rw [min_eq_right h2.le, div_self (up_pos hE hy).ne', one_mul]
        rw [hkx, hky]; linarith
  refine ⟨equity_anti hE hf, hmono, ?_⟩
  intro x hx y hy hxy
  simp only
  have hpx : 0 < E.qbp f x + E.equity f x := by
    have := qbp_ge hE hf hx; have := equity_nonneg hE hf x; have := hE.lo_pos; linarith
  have hpy : 0 < E.qbp f y + E.equity f y := by
    have := qbp_ge hE hf hy; have := equity_nonneg hE hf y; have := hE.lo_pos; linarith
  calc E.equity f y / (E.qbp f y + E.equity f y) ≤ E.equity f x / (E.qbp f y + E.equity f y) :=
        div_le_div_of_nonneg_right (equity_anti hE hf hx hy hxy) hpy.le
    _ ≤ E.equity f x / (E.qbp f x + E.equity f x) :=
        div_le_div_of_nonneg_left (equity_nonneg hE hf x) hpx (hmono hx hy hxy)

theorem lemma3 (hE : E.Valid) (hA3 : E.Assumption3) {f : ℝ → ℝ} (hf : E.IsDensity f) :
    MonotoneOn (fun x => x / E.qbp f x - 1) (Icc E.lo E.hi) := by
  have hlo := hE.lo_pos
  have hh := (marginal hE hA3).2
  intro x hx y hy hxy
  simp only
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hqx : 0 < E.qbp f x := by linarith [qbp_ge hE hf hx]
  have hqy : 0 < E.qbp f y := by linarith [qbp_ge hE hf hy]
  -- q(y)/y ≤ q(x)/x
  have key : E.qbp f y / y ≤ E.qbp f x / x := by
    rw [qbp_eq, qbp_eq]; unfold Q
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono_on hE.lo_lt_hi.le
      ((ker_int hE hf.integrable hy).div_const y) ((ker_int hE hf.integrable hx).div_const x)
    intro ω hω
    rw [mul_div_right_comm, mul_div_right_comm (ker E x ω)]
    apply mul_le_mul_of_nonneg_right _ (hf.nonneg ω hω)
    have hpw := up_pos hE hω
    have hpx := up_pos hE hx
    have hpy := up_pos hE hy
    have hkx1 : ω ≤ x → ker E x ω / x =
        deriv E.u (E.e1 + E.K * ω) * ω / (deriv E.u (E.e1 + E.K * x) * x) := fun h => by
      unfold ker; rw [min_eq_left h]; field_simp
    have hky1 : ω ≤ y → ker E y ω / y =
        deriv E.u (E.e1 + E.K * ω) * ω / (deriv E.u (E.e1 + E.K * y) * y) := fun h => by
      unfold ker; rw [min_eq_left h]; field_simp
    have hkx2 : x ≤ ω → ker E x ω / x = 1 := fun h => by
      unfold ker; rw [min_eq_right h, div_self hpx.ne', one_mul, div_self hx0.ne']
    have hky2 : y ≤ ω → ker E y ω / y = 1 := fun h => by
      unfold ker; rw [min_eq_right h, div_self hpy.ne', one_mul, div_self hy0.ne']
    have hmono : ∀ a ∈ Icc E.lo E.hi, ∀ b ∈ Icc E.lo E.hi, a ≤ b →
        deriv E.u (E.e1 + E.K * a) * a ≤ deriv E.u (E.e1 + E.K * b) * b :=
      fun a ha b hb hab => hh.monotoneOn ha hb hab
    have hw0 : 0 < ω := by linarith [hω.1]
    rcases le_or_gt ω x with h1 | h1
    · rw [hkx1 h1, hky1 (h1.trans hxy)]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact hmono x hx y hy hxy
    · rw [hkx2 h1.le]
      rcases le_or_gt ω y with h2 | h2
      · rw [hky1 h2, div_le_one (by positivity)]
        exact hmono ω hω y hy h2
      · rw [hky2 h2.le]
  rw [div_le_div_iff₀ hy0 hx0] at key
  have : x / E.qbp f x ≤ y / E.qbp f y := by
    rw [div_le_div_iff₀ hqx hqy]; linarith
  linarith

/-! ### the shocked economy -/

structure Ctx (E : Economy) (f ψ : ℝ → ℝ) (τ₀ : ℝ) : Prop where
  hE : E.Valid
  hA3 : E.Assumption3
  hf : E.IsDensity f
  hA2 : E.Assumption2 f
  hψ : E.IsDownsideImprovement (E.faceValue f) ψ
  hτ₀ : 0 < τ₀
  hdens : ∀ τ ∈ Icc 0 τ₀, ∀ ω ∈ Icc E.lo E.hi, 0 ≤ shock f ψ τ ω

lemma Ici_diff_zero : Ici (0:ℝ) \ {0} = Ioi 0 := by
  ext t; simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
  · intro h; exact ⟨h.le, h.ne'⟩

namespace Ctx
variable {f ψ : ℝ → ℝ} {τ₀ : ℝ} (c : Ctx E f ψ τ₀)
include c

lemma xs_mem : E.faceValue f ∈ Ioo E.lo E.hi := (theorem1 c.hE c.hf c.hA2).2.2

lemma xs_memI : E.faceValue f ∈ Icc E.lo E.hi := Ioo_subset_Icc_self c.xs_mem

lemma xs_root : E.faceValue f + Q E f (E.faceValue f) = E.D := (theorem1 c.hE c.hf c.hA2).2.1.2

lemma dens {τ : ℝ} (hτ : τ ∈ Icc 0 τ₀) : E.IsDensity (shock f ψ τ) where
  nonneg := c.hdens τ hτ
  integrable := c.hf.integrable.add (c.hψ.integrable.const_mul τ)
  total := by
    unfold shock
    rw [intervalIntegral.integral_add c.hf.integrable (c.hψ.integrable.const_mul τ),
      intervalIntegral.integral_const_mul, psi_total c.hE c.xs_memI c.hψ, c.hf.total]
    ring

lemma Qpsi_hi : 0 < Q E ψ E.hi := Qpsi_pos c.hE c.hA3 c.xs_memI c.hψ ⟨c.xs_memI.2, le_rfl⟩

lemma A2 {τ : ℝ} (hτ : τ ∈ Icc 0 τ₀) : E.Assumption2 (shock f ψ τ) := by
  refine ⟨c.hA2.1, ?_⟩
  have h := c.hA2.2
  have hhi : E.hi ∈ Icc E.lo E.hi := ⟨c.hE.lo_lt_hi.le, le_rfl⟩
  rw [← qbp_hi c.hE] at h ⊢
  rw [qbp_eq, Q_add c.hE c.hf.integrable c.hψ.integrable τ hhi]
  rw [qbp_eq] at h
  have := mul_nonneg hτ.1 c.Qpsi_hi.le
  linarith

lemma fv {τ : ℝ} (hτ : τ ∈ Icc 0 τ₀) :
    E.IsFaceValue (shock f ψ τ) (E.faceValue (shock f ψ τ)) ∧
      E.faceValue (shock f ψ τ) ∈ Ioo E.lo E.hi :=
  (theorem1 c.hE (c.dens hτ) (c.A2 hτ)).2

lemma root {τ : ℝ} (hτ : τ ∈ Icc 0 τ₀) :
    E.faceValue (shock f ψ τ) + Q E f (E.faceValue (shock f ψ τ)) +
      τ * Q E ψ (E.faceValue (shock f ψ τ)) = E.D := by
  have h := (c.fv hτ).1
  rw [← h.2, qbp_eq, Q_add c.hE c.hf.integrable c.hψ.integrable τ h.1]; ring

lemma shock0 : shock f ψ 0 = f := by funext ω; simp [shock]

lemma x0 : E.faceValue (shock f ψ 0) = E.faceValue f := by rw [c.shock0]

lemma lt {τ : ℝ} (hτ : τ ∈ Ioc 0 τ₀) : E.faceValue (shock f ψ τ) < E.faceValue f := by
  have hτ' : τ ∈ Icc 0 τ₀ := Ioc_subset_Icc_self hτ
  by_contra h
  push Not at h
  have hG := (G_strictMono c.hE (c.dens hτ')).monotoneOn c.xs_memI (c.fv hτ').1.1 h
  try simp only at hG
  rw [(c.fv hτ').1.2, qbp_eq, Q_add c.hE c.hf.integrable c.hψ.integrable τ c.xs_memI] at hG
  have hp : 0 < Q E ψ (E.faceValue f) := Qpsi_pos c.hE c.hA3 c.xs_memI c.hψ ⟨le_rfl, c.xs_memI.2⟩
  have := mul_pos hτ.1 hp
  have := c.xs_root
  linarith

lemma tend : Tendsto (fun τ => E.faceValue (shock f ψ τ)) (𝓝[>] 0) (𝓝 (E.faceValue f)) := by
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Ioc 0 τ₀ := Ioc_mem_nhdsGT c.hτ₀
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a E.lo with hal | hal
    · filter_upwards [hev] with τ hτ
      exact hal.trans (c.fv (Ioc_subset_Icc_self hτ)).2.1
    · have haI : a ∈ Icc E.lo E.hi := ⟨hal, ha.le.trans c.xs_memI.2⟩
      have hGa : a + E.qbp f a < E.D := by
        have := G_strictMono c.hE c.hf haI c.xs_memI ha
        simp only [qbp_eq] at this ⊢; linarith [c.xs_root]
      have hlim : Tendsto (fun τ => τ * Q E ψ a) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have : Tendsto (fun τ : ℝ => τ * Q E ψ a) (𝓝 (0:ℝ)) (𝓝 (0 * Q E ψ a)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      filter_upwards [hev, hlim.eventually (gt_mem_nhds (sub_pos.mpr hGa))] with τ hτ hτa
      have hτ' : τ ∈ Icc 0 τ₀ := Ioc_subset_Icc_self hτ
      by_contra hle
      push Not at hle
      have hG := (G_strictMono c.hE (c.dens hτ')).monotoneOn (c.fv hτ').1.1 haI hle
      try simp only at hG
      rw [(c.fv hτ').1.2, qbp_eq, Q_add c.hE c.hf.integrable c.hψ.integrable τ haI] at hG
      try simp only [qbp_eq] at hGa hτa
      linarith
  · filter_upwards [hev] with τ hτ
    exact (c.lt hτ).trans hb

lemma tendI : Tendsto (fun τ => E.faceValue (shock f ψ τ)) (𝓝[>] 0)
    (𝓝[Icc E.lo E.hi] (E.faceValue f)) :=
  tendsto_nhdsWithin_iff.2 ⟨c.tend, by
    filter_upwards [Ioc_mem_nhdsGT c.hτ₀] with τ hτ
    exact Ioo_subset_Icc_self (c.fv (Ioc_subset_Icc_self hτ)).2⟩

theorem eq34 :
    HasDerivWithinAt (fun τ => E.faceValue (shock f ψ τ))
        (-E.dqTau ψ (E.faceValue f) / (1 + E.dqbp f (E.faceValue f))) (Ici 0) 0 ∧
      -E.dqTau ψ (E.faceValue f) / (1 + E.dqbp f (E.faceValue f)) < 0 := by
  set xs := E.faceValue f with hxs
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Ioc 0 τ₀ := Ioc_mem_nhdsGT c.hτ₀
  have hB := eqB1 c.hE c.hf xs c.xs_mem
  have hc0 : 0 < 1 + E.dqbp f xs := by linarith [hB.2]
  have hQ : Q E ψ xs = E.dqTau ψ xs := Qpsi_eq c.hE c.xs_memI c.hψ ⟨le_rfl, c.xs_memI.2⟩
  have hdq : 0 < E.dqTau ψ xs := (footnote26 c.hE c.hA3 c.hf c.hA2 c.hψ).2
  refine ⟨?_, div_neg_of_neg_of_pos (neg_neg_of_pos hdq) hc0⟩
  have hφ : HasDerivAt (fun y => y + E.qbp f y) (1 + E.dqbp f xs) xs := (hasDerivAt_id' xs).add hB.1
  have hslope := hasDerivAt_iff_tendsto_slope.1 hφ
  have htend' : Tendsto (fun τ => E.faceValue (shock f ψ τ)) (𝓝[>] 0) (𝓝[≠] xs) :=
    tendsto_nhdsWithin_iff.2 ⟨c.tend, hev.mono fun τ hτ => (c.lt hτ).ne⟩
  have hQc : Tendsto (fun τ => Q E ψ (E.faceValue (shock f ψ τ))) (𝓝[>] 0) (𝓝 (Q E ψ xs)) :=
    ((Q_cont c.hE c.hψ.integrable) xs c.xs_memI).tendsto.comp c.tendI
  have hlim := hQc.neg.div (hslope.comp htend') hc0.ne'
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_zero, ← hQ]
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  have hτ' : τ ∈ Icc 0 τ₀ := Ioc_subset_Icc_self hτ
  have hlt := c.lt hτ
  have hr := c.root hτ'
  have hxr := c.xs_root
  have hxtI := Ioo_subset_Icc_self (c.fv hτ').2
  have hQt : 0 < Q E ψ (E.faceValue (shock f ψ τ)) := by
    have hG := G_strictMono c.hE c.hf hxtI c.xs_memI hlt
    simp only at hG; rw [qbp_eq, qbp_eq] at hG
    nlinarith [hτ.1]
  simp only [Pi.div_apply, Function.comp_apply, slope_def_field, c.x0, qbp_eq]
  have hne : E.faceValue (shock f ψ τ) - xs ≠ 0 := sub_ne_zero.mpr hlt.ne
  have e1 : E.faceValue (shock f ψ τ) + Q E f (E.faceValue (shock f ψ τ)) - (xs + Q E f xs) =
      -(τ * Q E ψ (E.faceValue (shock f ψ τ))) := by linarith
  rw [e1]
  have hτ0 : τ ≠ 0 := hτ.1.ne'
  field_simp
  ring

lemma bp {τ : ℝ} (hτ : τ ∈ Icc 0 τ₀) :
    E.bondPrice (shock f ψ τ) = E.D - E.faceValue (shock f ψ τ) := by
  have h := (c.fv hτ).1.2
  unfold bondPrice; linarith

lemma Dpos : 0 < E.D := by have := c.hA2.1; have := c.hE.lo_pos; linarith

lemma xs_lt_D : E.faceValue f < E.D := by
  have := D_sub_pos c.hE c.hf (theorem1 c.hE c.hf c.hA2).2.1; linarith

theorem eq35 :
    HasDerivWithinAt
      (fun τ => E.equity (shock f ψ τ) (E.faceValue (shock f ψ τ)) / E.bondPrice (shock f ψ τ))
      (-E.dqTau ψ (E.faceValue f) /
          (E.bondPrice f ^ 2 * (1 + E.dqbp f (E.faceValue f))) * E.margin f (E.faceValue f))
      (Ici 0) 0 := by
  set xs := E.faceValue f with hxs
  have hx' := c.eq34.1
  have hxD := c.xs_lt_D
  have hB := eqB1 c.hE c.hf xs c.xs_mem
  have hc0 : 0 < 1 + E.dqbp f xs := by linarith [hB.2]
  have hΦ := Phi_hasDeriv c.hE c.hf c.xs_mem hxD
  have h1 := hΦ.comp_hasDerivWithinAt_of_eq 0 hx' c.x0.symm
  set r : ℝ → ℝ := fun τ => Eqty E ψ (E.faceValue (shock f ψ τ)) / (E.D - E.faceValue (shock f ψ τ))
    with hr
  have hrt : Tendsto r (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun τ => Eqty E ψ (E.faceValue (shock f ψ τ))) (𝓝[>] 0)
        (𝓝 (Eqty E ψ xs)) := ((Eq_cont c.hE c.hψ.integrable).tendsto xs).comp c.tend
    rw [Eq_psi_zero c.hE c.hψ] at h0
    have h2 : Tendsto (fun τ => E.D - E.faceValue (shock f ψ τ)) (𝓝[>] 0) (𝓝 (E.D - xs)) :=
      tendsto_const_nhds.sub c.tend
    have := h0.div h2 (by linarith)
    rwa [zero_div] at this
  have h2 : HasDerivWithinAt (fun τ => τ * r τ) 0 (Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_zero]
    refine hrt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simp only [slope_def_field, zero_mul, sub_zero]
    field_simp [(mem_Ioi.mp hτ).ne']
  have h3 := h1.add h2
  have hJ : (fun τ => E.equity (shock f ψ τ) (E.faceValue (shock f ψ τ)) / E.bondPrice (shock f ψ τ))
      =ᶠ[𝓝[Ici 0] 0] ((fun y => E.equity f y / (E.D - y)) ∘ (fun τ => E.faceValue (shock f ψ τ)) +
        fun τ => τ * r τ) := by
    filter_upwards [Icc_mem_nhdsGE c.hτ₀] with τ hτ
    simp only [Pi.add_apply, Function.comp_apply, hr]
    rw [c.bp hτ, equity_eq, Eq_add c.hE c.hf.integrable c.hψ.integrable, add_div, mul_div_assoc,
      equity_eq]
  refine (h3.congr_of_eventuallyEq_of_mem hJ (mem_Ici.mpr le_rfl)).congr_deriv ?_
  have hbp : E.bondPrice f = E.D - xs := by
    have := c.xs_root; unfold bondPrice; rw [qbp_eq]; linarith
  have hne : E.D - xs ≠ 0 := by linarith
  have hc0' := hc0.ne'
  rw [hxs] at hne hbp hc0'
  rw [hbp]
  field_simp
  ring

end Ctx

namespace Ctx
variable {f ψ : ℝ → ℝ} {τ₀ : ℝ} (c : Ctx E f ψ τ₀)
include c

theorem part1 : ∀ τ ∈ Ioc 0 τ₀,
      E.faceValue (shock f ψ τ) < E.faceValue f ∧
      E.rate (shock f ψ τ) < E.rate f ∧
      E.assetPrice f < E.assetPrice (shock f ψ τ) := by
  intro τ hτ
  have hτ' : τ ∈ Icc 0 τ₀ := Ioc_subset_Icc_self hτ
  have hlt := c.lt hτ
  have hxD := c.xs_lt_D
  have hD := c.Dpos
  have hbp0 : E.bondPrice f = E.D - E.faceValue f := by
    have := c.xs_root; unfold bondPrice; rw [qbp_eq]; linarith
  have hbpt := c.bp hτ'
  refine ⟨hlt, ?_, ?_⟩
  · unfold rate
    rw [hbp0, hbpt]
    have h1 : 0 < E.D - E.faceValue (shock f ψ τ) := by linarith
    have h2 : 0 < E.D - E.faceValue f := by linarith
    have : E.faceValue (shock f ψ τ) / (E.D - E.faceValue (shock f ψ τ)) <
        E.faceValue f / (E.D - E.faceValue f) := by
      rw [div_lt_div_iff₀ h1 h2]; nlinarith
    linarith
  · unfold assetPrice
    rw [hbp0, hbpt, equity_eq, equity_eq, Eq_add c.hE c.hf.integrable c.hψ.integrable]
    have hxtI := Ioo_subset_Icc_self (c.fv hτ').2
    have h1 := equity_anti c.hE c.hf hxtI c.xs_memI hlt.le
    rw [equity_eq, equity_eq] at h1
    have h2 := mul_nonneg hτ.1.le (Eq_psi_nonneg c.hE c.xs_memI c.hψ (E.faceValue (shock f ψ τ)))
    linarith

lemma J_nonneg {τ : ℝ} (hτ : τ ∈ Icc 0 τ₀) :
    0 ≤ E.equity (shock f ψ τ) (E.faceValue (shock f ψ τ)) / E.bondPrice (shock f ψ τ) := by
  apply div_nonneg (equity_nonneg c.hE (c.dens hτ) _)
  unfold bondPrice
  have := qbp_ge c.hE (c.dens hτ) (Ioo_subset_Icc_self (c.fv hτ).2)
  have := c.hE.lo_pos
  linarith

theorem part2 : ∃ d : ℝ, HasDerivWithinAt (fun τ => E.haircut (shock f ψ τ)) d (Ici 0) 0 ∧
      (d < 0 ↔ (1 - E.cdf f (E.faceValue f)) * E.D < ∫ ω in E.faceValue f..E.hi, ω * f ω) := by
  set J := fun τ => E.equity (shock f ψ τ) (E.faceValue (shock f ψ τ)) / E.bondPrice (shock f ψ τ)
    with hJdef
  set J' := -E.dqTau ψ (E.faceValue f) /
          (E.bondPrice f ^ 2 * (1 + E.dqbp f (E.faceValue f))) * E.margin f (E.faceValue f)
    with hJ'def
  have hJ : HasDerivWithinAt J J' (Ici 0) 0 := c.eq35
  have hJ0 : 0 ≤ J 0 := c.J_nonneg ⟨le_rfl, c.hτ₀.le⟩
  have hne : (1 + J 0) ≠ 0 := by linarith
  have hH := hJ.div (hJ.const_add 1) hne
  have hev : (fun τ => E.haircut (shock f ψ τ)) =ᶠ[𝓝[Ici 0] 0] fun τ => J τ / (1 + J τ) := by
    filter_upwards [Icc_mem_nhdsGE c.hτ₀] with τ hτ
    simp only [hJdef]
    unfold haircut assetPrice
    have hb : 0 < E.bondPrice (shock f ψ τ) := by
      unfold bondPrice
      have := qbp_ge c.hE (c.dens hτ) (Ioo_subset_Icc_self (c.fv hτ).2)
      have := c.hE.lo_pos
      linarith
    have he := equity_nonneg c.hE (c.dens hτ) (E.faceValue (shock f ψ τ))
    field_simp
  refine ⟨_, hH.congr_of_eventuallyEq_of_mem hev (mem_Ici.mpr le_rfl), ?_⟩
  have hnum : J' * (1 + J 0) - J 0 * J' = J' := by ring
  rw [hnum]
  have hsq : 0 < (1 + J 0) ^ 2 := by positivity
  have hB := eqB1 c.hE c.hf _ c.xs_mem
  have hc0 : 0 < 1 + E.dqbp f (E.faceValue f) := by linarith [hB.2]
  have hdq : 0 < E.dqTau ψ (E.faceValue f) := (footnote26 c.hE c.hA3 c.hf c.hA2 c.hψ).2
  have hbp : 0 < E.bondPrice f := by
    unfold bondPrice
    have := qbp_ge c.hE c.hf c.xs_memI
    have := c.hE.lo_pos
    linarith
  have hk : -E.dqTau ψ (E.faceValue f) / (E.bondPrice f ^ 2 * (1 + E.dqbp f (E.faceValue f))) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hdq) (by positivity)
  have hiff : J' < 0 ↔ 0 < E.margin f (E.faceValue f) := by
    rw [hJ'def]
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  constructor
  · intro h
    have hJn : J' < 0 := by
      by_contra h'; push Not at h'; have := div_nonneg h' hsq.le; linarith
    have := hiff.1 hJn
    unfold margin at this; linarith
  · intro h
    have hm : 0 < E.margin f (E.faceValue f) := by unfold margin; linarith
    exact div_neg_of_neg_of_pos (hiff.2 hm) hsq

end Ctx

end HaircutRate.Downside.HLib

open Set HaircutRate.Downside HaircutRate.Downside.Economy

theorem solution (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3) (f : ℝ → ℝ)
    (hf : E.IsDensity f) (hA2 : E.Assumption2 f)
    (ψ : ℝ → ℝ) (hψ : E.IsDownsideImprovement (E.faceValue f) ψ)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hdens : ∀ τ ∈ Icc 0 τ₀, ∀ ω ∈ Icc E.lo E.hi, 0 ≤ shock f ψ τ ω) :
    HasDerivWithinAt
      (fun τ => E.equity (shock f ψ τ) (E.faceValue (shock f ψ τ)) / E.bondPrice (shock f ψ τ))
      (-E.dqTau ψ (E.faceValue f) /
          (E.bondPrice f ^ 2 * (1 + E.dqbp f (E.faceValue f))) * E.margin f (E.faceValue f))
      (Ici 0) 0 :=
  (HLib.Ctx.mk hE hA3 hf hA2 hψ hτ₀ hdens).eq35
