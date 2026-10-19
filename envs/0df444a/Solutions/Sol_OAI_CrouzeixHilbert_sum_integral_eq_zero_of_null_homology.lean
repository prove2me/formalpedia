-- Prove2me | solution 1 for OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:43:45.581073+00:00
-- url     : https://prove2.me/submissions/df8fcd57-1b64-4b1d-8e33-149f707fb985

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Existence. -/

noncomputable section

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

open Set Filter Metric

namespace CrouzeixHilbert

theorem sub_div_sub_mem_slitPlane {a b w : ℂ} (hw : w ∉ segment ℝ a b) :
    (w - a) / (w - b) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hwb : w - b ≠ 0 := by
    intro he
    exact hw ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  let r : ℝ := ((w - a) / (w - b)).re
  have hr : r ≤ 0 := h.1
  have hrc : (r : ℂ) = (w - a) / (w - b) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using h.2.symm
  have hmul : (r : ℂ) * (w - b) = w - a := by rw [hrc, div_mul_cancel₀ _ hwb]
  have hp : 0 < 1 - r := by linarith
  have hpn : (1 - (r : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  apply hw
  refine ⟨(1 - r)⁻¹, -r / (1 - r), inv_nonneg.mpr hp.le,
    div_nonneg (neg_nonneg.mpr hr) hp.le, ?_, ?_⟩
  · field_simp
    ring
  · simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg]
    apply (mul_right_cancel₀ hpn)
    field_simp
    linear_combination hmul

theorem SmoothContour.intervalIntegrable_indexIntegrand (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.path '' Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => deriv Γ.path t / (Γ.path t - a))
      MeasureTheory.volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  apply Γ.smooth.continuous_deriv_one.continuousOn.div
    (Γ.smooth.continuous.sub continuous_const).continuousOn
  intro t ht he
  exact ha ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.index_eq_of_segment_avoids (Γ : SmoothContour) {a b : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Γ.path t ∉ segment ℝ a b) :
    Γ.index a = Γ.index b := by
  have hnza (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ left_mem_segment ℝ a b)
  have hnzb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - b ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnza t ht (sub_eq_zero.mpr he)
  have hb : b ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnzb t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log ((Γ.path t - a) / (Γ.path t - b)))
        (deriv Γ.path t / (Γ.path t - a) - deriv Γ.path t / (Γ.path t - b)) t := by
    have hg := (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
    have he := ((hg.sub_const a).div (hg.sub_const b) (hnzb t ht)).clog_real
      (sub_div_sub_mem_slitPlane (h t ht))
    simp only [Pi.div_apply] at he
    convert! he using 1
    field_simp [hnza t ht, hnzb t ht]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    ((Γ.intervalIntegrable_indexIntegrand ha).sub (Γ.intervalIntegrable_indexIntegrand hb))
  rw [Γ.closed, sub_self, intervalIntegral.integral_sub
    (Γ.intervalIntegrable_indexIntegrand ha) (Γ.intervalIntegrable_indexIntegrand hb)] at he
  unfold SmoothContour.index
  rw [sub_eq_zero.mp he]

theorem SmoothContour.index_eq_zero_of_re_pos (Γ : SmoothContour) {a c : ℂ}
    (hc : c ≠ 0) (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c * (Γ.path t - a)).re) :
    Γ.index a = 0 := by
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    simpa only [he, mul_zero, Complex.zero_re, lt_self_iff_false] using h t ht
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnz t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log (c * (Γ.path t - a)))
        (deriv Γ.path t / (Γ.path t - a)) t := by
    have he := (((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).const_mul c).clog_real
      (Complex.mem_slitPlane_iff.mpr (Or.inl (h t ht)))
    simpa only [mul_div_mul_left _ _ hc] using he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (Γ.intervalIntegrable_indexIntegrand ha)
  rw [Γ.closed, sub_self] at he
  simp only [SmoothContour.index, he, mul_zero]

theorem SmoothContour.index_eq_zero_of_convex (Γ : SmoothContour) {V : Set ℂ}
    (hV : Convex ℝ V) (hVc : IsClosed V) (hΓ : Γ.path '' Icc (0 : ℝ) 1 ⊆ V)
    {a : ℂ} (ha : a ∉ V) :
    Γ.index a = 0 := by
  obtain ⟨l, r, hla, hlV⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hV hVc ha
  have hl (z : ℂ) : l z = l 1 * z := by
    calc
      l z = l (z • (1 : ℂ)) := by simp
      _ = z • l 1 := l.map_smul z 1
      _ = l 1 * z := by simp [mul_comm]
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < (l 1 * (Γ.path t - a)).re := by
    rw [← hl, map_sub, Complex.sub_re]
    exact sub_pos.mpr (hla.trans (hlV _ (hΓ ⟨t, ht, rfl⟩)))
  apply Γ.index_eq_zero_of_re_pos ?_ hp
  intro he
  have := hp 0 ⟨le_rfl, zero_le_one⟩
  simp only [he, zero_mul, Complex.zero_re, lt_self_iff_false] at this

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.isCompact_trace (Γ : SmoothContour) : IsCompact Γ.trace :=
  isCompact_Icc.image Γ.smooth.continuous

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HomologicalCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homological Cauchy. -/

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

theorem SmoothContour.intervalIntegrable_contourIntegrand {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Γ : SmoothContour) {f : ℂ → E}
    (hf : ContinuousOn f Γ.trace) :
    IntervalIntegrable (fun t => deriv Γ.path t • f (Γ.path t)) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  exact Γ.smooth.continuous_deriv_one.continuousOn.smul
    (hf.comp Γ.smooth.continuous.continuousOn (fun t ht => ⟨t, ht, rfl⟩))

theorem SmoothContour.differentiableOn_cauchyTransform {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace) :
    DifferentiableOn ℂ (Γ.cauchyTransform f) Γ.traceᶜ := by
  apply DifferentiableOn.const_smul
  apply differentiableOn_parameter_intervalIntegral Γ.isCompact_trace.isClosed.isOpen_compl
  · have hc : Continuous (fun p : ℂ × ℝ => deriv Γ.path p.2) :=
      Γ.smooth.continuous_deriv_one.comp continuous_snd
    apply hc.continuousOn.smul
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact ((Γ.smooth.continuous.comp continuous_snd).sub continuous_fst).continuousOn
      · intro p hp he
        exact hp.1 ⟨p.2, hp.2, sub_eq_zero.mp he⟩
    · exact hf.comp (Γ.smooth.continuous.comp continuous_snd).continuousOn
        (fun p hp => ⟨p.2, hp.2, rfl⟩)
  · intro t ht
    apply DifferentiableOn.const_smul
    apply DifferentiableOn.smul_const
    apply DifferentiableOn.inv
    · exact ((differentiable_const (Γ.path t)).sub differentiable_id).differentiableOn
    · intro w hw he
      exact hw ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.differentiableOn_regularizedTransform {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.trace ⊆ U)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (Γ.regularizedTransform f) U := by
  apply DifferentiableOn.const_smul
  apply differentiableOn_parameter_intervalIntegral hU
  · apply (Γ.smooth.continuous_deriv_one.comp continuous_snd).continuousOn.smul
    apply (continuousOn_dslope_pair hU hf).comp
      (continuous_fst.prodMk (Γ.smooth.continuous.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1, hΓ ⟨p.2, hp.2, rfl⟩⟩
  · intro t ht
    apply DifferentiableOn.const_smul
    have hd := (Complex.differentiableOn_dslope (hU.mem_nhds (hΓ ⟨t, ht, rfl⟩))).mpr hf
    exact hd.congr (fun w _ => dslope_swap f w (Γ.path t))

theorem SmoothContour.regularizedTransform_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace)
    {w : ℂ} (hw : w ∉ Γ.trace) :
    Γ.regularizedTransform f w = Γ.cauchyTransform f w - Γ.index w • f w := by
  have hc : ContinuousOn (fun z : ℂ => (z - w)⁻¹) Γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      (fun z hz he => hw ((show z = w from sub_eq_zero.mp he) ▸ hz))
  have hi : IntervalIntegrable (fun t => deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t)))
      volume (0 : ℝ) 1 := by
    simpa only [Pi.smul_apply'] using Γ.intervalIntegrable_contourIntegrand (hc.smul hf)
  have hj := (Γ.intervalIntegrable_indexIntegrand hw).smul_continuousOn
    (continuousOn_const (c := f w))
  unfold SmoothContour.regularizedTransform SmoothContour.cauchyTransform SmoothContour.integral
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t • dslope f w (Γ.path t)) =
      (∫ t in (0 : ℝ)..1, deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t))) -
      (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - w)) • f w := by
    rw [← intervalIntegral.integral_smul_const, ← intervalIntegral.integral_sub hi hj]
    apply intervalIntegral.integral_congr
    intro t ht
    have hn : Γ.path t ≠ w := fun he => hw ⟨t, by simpa only [uIcc_of_le zero_le_one] using ht, he⟩
    simp only [dslope_of_ne f hn, slope, vsub_eq_sub, smul_sub, smul_smul, div_eq_mul_inv]
  rw [he, smul_sub, smul_smul]
  rfl

theorem SmoothContour.eventually_index_eq (Γ : SmoothContour) {w : ℂ}
    (hw : w ∉ Γ.trace) : ∀ᶠ z in 𝓝 w, Γ.index z = Γ.index w := by
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp
    (Γ.isCompact_trace.isClosed.isOpen_compl.mem_nhds hw)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  apply Γ.index_eq_of_segment_avoids
  intro t ht he
  exact hrc ((convex_ball w r).segment_subset hz (mem_ball_self hr) he) ⟨t, ht, rfl⟩

theorem SmoothContour.tendsto_cauchyTransform_cocompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace) :
    Tendsto (Γ.cauchyTransform f) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn continuousOn_id
  have hc : ContinuousOn (fun t => deriv Γ.path t • f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    Γ.smooth.continuous_deriv_one.continuousOn.smul
      (hf.comp Γ.smooth.continuous.continuousOn (fun t ht => ⟨t, ht, rfl⟩))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have htop : Tendsto (fun w : ℂ => ‖w‖ - R) (cocompact ℂ) atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right (cocompact ℂ) (-R) tendsto_norm_cocompact_atTop
  have hb : ∀ᶠ w : ℂ in cocompact ℂ,
      ‖∫ t in (0 : ℝ)..1, deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t))‖ ≤
      (‖w‖ - R)⁻¹ * M := by
    filter_upwards [htop.eventually_gt_atTop 0] with w hw
    have hi := @intervalIntegral.norm_integral_le_of_norm_le_const E _ _
      0 1 ((‖w‖ - R)⁻¹ * M)
      (fun t => deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t)))
    simpa only [sub_zero, abs_one, mul_one] using hi (by
      intro t ht
      have htt : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
      have hn : ‖w‖ - R ≤ ‖Γ.path t - w‖ := by
        have hne := norm_sub_norm_le w (Γ.path t)
        rw [norm_sub_rev] at hne
        have hr : ‖Γ.path t‖ ≤ R := hR _ ⟨t, htt, rfl⟩
        linarith
      have he : ‖deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t))‖ =
          ‖Γ.path t - w‖⁻¹ * ‖deriv Γ.path t • f (Γ.path t)‖ := by
        simp only [norm_smul, norm_inv]
        ring
      rw [he]
      exact mul_le_mul (inv_anti₀ hw hn) (hM t htt) (norm_nonneg _) (by positivity))
  have hl : Tendsto (fun w : ℂ => (‖w‖ - R)⁻¹ * M) (cocompact ℂ) (𝓝 0) := by
    simpa only [Pi.inv_apply, zero_mul] using htop.inv_tendsto_atTop.mul_const M
  have hi := squeeze_zero_norm' hb hl
  change Tendsto (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t)))
      (cocompact ℂ) (𝓝 0)
  simpa only [smul_zero] using hi.const_smul (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem SmoothContour.eventually_index_zero_cocompact (Γ : SmoothContour) :
    ∀ᶠ w : ℂ in cocompact ℂ, w ∉ Γ.trace ∧ Γ.index w = 0 := by
  obtain ⟨R, hR⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn continuousOn_id
  have hsub : Γ.trace ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right, id_eq] using hR z hz
  filter_upwards [(isCompact_closedBall (0 : ℂ) R).compl_mem_cocompact] with w hw
  exact ⟨fun h => hw (hsub h), Γ.index_eq_zero_of_convex (convex_closedBall 0 R)
    isClosed_closedBall hsub hw⟩

theorem SmoothContour.tendsto_regularizedTransform_cocompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace) :
    Tendsto (Γ.regularizedTransform f) (cocompact ℂ) (𝓝 0) := by
  apply (Γ.tendsto_cauchyTransform_cocompact hf).congr'
  filter_upwards [Γ.eventually_index_zero_cocompact] with w hw
  rw [Γ.regularizedTransform_eq hf hw.1, hw.2, zero_smul, sub_zero]

theorem sum_regularizedTransform_eq_zero {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (w : ℂ) :
    ∑ i, c i • (Γ i).regularizedTransform f w = 0 := by
  let g : ℂ → E := fun z => ∑ i, c i • (Γ i).regularizedTransform f z
  have hfc (i : ι) : ContinuousOn f (Γ i).trace := hf.continuousOn.mono (hΓ i)
  have heq (v : ℂ) (hv : ∀ i, v ∉ (Γ i).trace) : g v =
      (∑ i, c i • (Γ i).cauchyTransform f v) - (∑ i, c i * (Γ i).index v) • f v := by
    dsimp only [g]
    simp_rw [(Γ _).regularizedTransform_eq (hfc _) (hv _), smul_sub, smul_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_smul]
  have hd : Differentiable ℂ g := by
    intro v
    by_cases hv : v ∈ U
    · apply DifferentiableAt.fun_sum
      intro i _
      exact ((Γ i).differentiableOn_regularizedTransform hU (hΓ i) hf
        |>.differentiableAt (hU.mem_nhds hv)).const_smul (c i)
    · have hvΓ (i : ι) : v ∉ (Γ i).trace := fun hi => hv (hΓ i hi)
      have hc : DifferentiableAt ℂ (fun z => ∑ i, c i • (Γ i).cauchyTransform f z) v := by
        apply DifferentiableAt.fun_sum
        intro i _
        exact ((Γ i).differentiableOn_cauchyTransform (hfc i)
          |>.differentiableAt ((Γ i).isCompact_trace.isClosed.isOpen_compl.mem_nhds (hvΓ i))).const_smul (c i)
      apply hc.congr_of_eventuallyEq
      have hi (i : ι) : ∀ᶠ z in 𝓝 v, z ∉ (Γ i).trace ∧ (Γ i).index z = (Γ i).index v :=
        (show ∀ᶠ z in 𝓝 v, z ∉ (Γ i).trace from
          (Γ i).isCompact_trace.isClosed.isOpen_compl.mem_nhds (hvΓ i)).and
          ((Γ i).eventually_index_eq (hvΓ i))
      filter_upwards [eventually_all.mpr hi] with z hz
      rw [heq z (fun i => (hz i).1)]
      have he : (∑ i, c i * (Γ i).index z) = 0 := by
        simpa only [(hz _).2] using hnull v hv
      rw [he, zero_smul, sub_zero]
  have ht : Tendsto g (cocompact ℂ) (𝓝 0) := by
    have hti (i : ι) := ((Γ i).tendsto_regularizedTransform_cocompact (hfc i)).const_smul (c i)
    simpa only [g, smul_zero, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hti i)
  exact hd.apply_eq_of_tendsto_cocompact w ht

theorem null_homology_integral_core {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • (Γ i).integral f = 0 := by
  have he := sum_regularizedTransform_eq_zero Γ c hU hΓ hnull
    (differentiableOn_id.fun_smul hf) 0
  convert! he using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold SmoothContour.regularizedTransform SmoothContour.integral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change deriv (Γ i).path t • f ((Γ i).path t) =
    deriv (Γ i).path t • dslope (fun z => z • f z) 0 ((Γ i).path t)
  congr 1
  have htU : (Γ i).path t ∈ U := hΓ i ⟨t, by simpa only [uIcc_of_le zero_le_one] using ht, rfl⟩
  by_cases hz : (Γ i).path t = 0
  · rw [hz, dslope_same]
    have hd := (hasDerivAt_id (0 : ℂ)).fun_smul
      ((hf.differentiableAt (hU.mem_nhds (hz ▸ htU))).hasDerivAt)
    simpa only [id_eq, one_smul, zero_smul, zero_add] using hd.deriv.symm
  · rw [dslope_of_ne _ hz]
    simp only [slope, vsub_eq_sub, sub_zero, zero_smul, inv_smul_smul₀ hz]

theorem sum_integral_eq_zero_of_null_homology_oai {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).path '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∫ t in (0 : ℝ)..1, deriv (Γ i).path t • f ((Γ i).path t)) = 0 :=
  null_homology_integral_core Γ c hU hΓ hnull hf

end CrouzeixHilbert

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology_oai.{u_1, u_2} := @OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology_oai.{u_1, u_2}
