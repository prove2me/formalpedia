-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7deea2f1-b0b0-543a-9080-d4d809c6a79a

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero

set_option autoImplicit false

open Complex

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "signEpsilon RealArchParam.epsilonFactor RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.centralExponent RealArchParam.centralSign RealArchParam.oddArtin RealArchParam.discrete RealArchParam.principal"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.psi ArchDatumR"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

noncomputable section

open MeasureTheory Set Filter Topology

namespace GammaRate

private theorem integrableOn_cpow_mul_exp_neg_mul {α w : ℂ} (hα : 0 < α.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * Complex.exp (-(α * t))) (Ioi 0) := by
  have hconv : MellinConvergent (fun t : ℝ => Complex.exp (-(α * t))) w := by
    refine mellinConvergent_of_isBigO_rpow_exp (a := α.re) (b := 0) hα ?_ ?_ ?_ (by simpa using hw)
    · exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
        ).locallyIntegrable.locallyIntegrableOn _
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      rw [Complex.norm_exp, one_mul, Real.norm_eq_abs, Real.abs_exp]
      apply le_of_eq
      congr 1
      simp [Complex.mul_re]
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [Complex.norm_exp, one_mul, neg_zero, Real.rpow_zero, norm_one]
      apply Real.exp_le_one_iff.mpr
      have : (-(α * (t : ℂ))).re = -(α.re * t) := by simp [Complex.mul_re]
      rw [this, neg_nonpos]
      positivity
  simpa [MellinConvergent, smul_eq_mul] using hconv

private def rateIntegral (w z : ℂ) : ℂ := ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (w - 1) * Complex.exp (-(z * t))

private theorem hasDerivAt_rateIntegral {w : ℂ} (hw : 0 < w.re) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (rateIntegral w)
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (w - 1) * (Complex.exp (-(z₀ * t)) * -(t : ℂ))) z₀ := by
  set δ : ℝ := z₀.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hw1 : 0 < (w + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith

  have hball : ∀ z ∈ Metric.ball z₀ δ, δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := (abs_le.mp h1).1
    linarith
  unfold rateIntegral
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun z (t : ℝ) => (t : ℂ) ^ (w - 1) * Complex.exp (-(z * t)))
    (F' := fun z (t : ℝ) => (t : ℂ) ^ (w - 1) * (Complex.exp (-(z * t)) * -(t : ℂ)))
    (bound := fun t : ℝ => ‖(t : ℂ) ^ w * Complex.exp (-((δ : ℂ) * t))‖)
    (Metric.ball_mem_nhds z₀ hδpos) ?_ ?_ ?_ ?_ ?_ ?_).2
  ·
    refine Eventually.of_forall fun z => ?_
    exact ((Complex.measurable_ofReal.pow_const (w - 1)).mul
      ((Complex.measurable_ofReal.const_mul z).neg.cexp)).aestronglyMeasurable
  · exact integrableOn_cpow_mul_exp_neg_mul hz₀ hw
  ·
    exact ((Complex.measurable_ofReal.pow_const (w - 1)).mul
      (((Complex.measurable_ofReal.const_mul z₀).neg.cexp).mul
        Complex.measurable_ofReal.neg)).aestronglyMeasurable
  ·
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 0 < t) z hz => ?_
    have hzre := hball z hz
    have e1 : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
    have e2 : (-((δ : ℂ) * (t : ℂ))).re = -(δ * t) := by simp [Complex.mul_re]
    simp only [norm_mul, norm_neg, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Complex.sub_re, Complex.one_re, e1, e2]
    have e3 : t ^ w.re = t ^ (w.re - 1) * t := by
      rw [← Real.rpow_add_one ht.ne', sub_add_cancel]
    have e4 : Real.exp (-(z.re * t)) ≤ Real.exp (-(δ * t)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hzre ht.le))
    have e5 : 0 ≤ t ^ (w.re - 1) := Real.rpow_nonneg ht.le _
    rw [e3]
    calc t ^ (w.re - 1) * (Real.exp (-(z.re * t)) * t)
        ≤ t ^ (w.re - 1) * (Real.exp (-(δ * t)) * t) := by gcongr
      _ = t ^ (w.re - 1) * t * Real.exp (-(δ * t)) := by ring
  ·
    have h := integrableOn_cpow_mul_exp_neg_mul (α := (δ : ℂ)) (w := w + 1) (by simpa using hδpos) hw1
    simpa only [add_sub_cancel_right] using h.norm
  ·
    refine Eventually.of_forall fun t z _ => ?_
    have h := ((((hasDerivAt_id z).mul_const (t : ℂ)).neg).cexp).const_mul ((t : ℂ) ^ (w - 1))
    simpa using h

private theorem analyticOnNhd_rateIntegral {w : ℂ} (hw : 0 < w.re) :
    AnalyticOnNhd ℂ (rateIntegral w) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) (isOpen_lt continuous_const Complex.continuous_re)
  exact (hasDerivAt_rateIntegral hw hz).differentiableAt.differentiableWithinAt

private theorem analyticOnNhd_rhs (w : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-w) * Complex.Gamma w) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) (isOpen_lt continuous_const Complex.continuous_re)
  have hz' : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  exact ((differentiableAt_id.cpow_const hz').mul_const _).differentiableWithinAt

private theorem rateIntegral_ofReal {w : ℂ} (hw : 0 < w.re) {r : ℝ} (hr : 0 < r) :
    rateIntegral w r = (r : ℂ) ^ (-w) * Complex.Gamma w := by
  unfold rateIntegral
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hr, one_div, Complex.cpow_neg,
    Complex.inv_cpow]
  rw [Complex.arg_ofReal_of_nonneg hr.le]
  exact Real.pi_pos.ne

private theorem integral_cpow_mul_exp_neg_mul_eq_cpow {α w : ℂ} (hα : 0 < α.re) (hw : 0 < w.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (w - 1) * Complex.exp (-(α * t)) = α ^ (-w) * Complex.Gamma w := by
  have hU : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp

  have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
      rw [add_zero] at h
      have h' : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp h
      rwa [Complex.ofReal_one] at h'
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), rateIntegral w z = z ^ (-w) * Complex.Gamma w :=
    hseq.frequently (Frequently.of_forall fun n => rateIntegral_ofReal hw (by positivity))
  have heq := (analyticOnNhd_rateIntegral hw).eqOn_of_preconnected_of_frequently_eq (analyticOnNhd_rhs w)
    hU h1 hfreq
  exact heq (show α ∈ {z : ℂ | 0 < z.re} from hα)

private theorem integral_cpow_mul_exp_neg_mul_eq_exp_log {α w : ℂ} (hα : 0 < α.re) (hw : 0 < w.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (w - 1) * Complex.exp (-(α * t))
      = Complex.Gamma w * Complex.exp (-(w * Complex.log α)) := by
  have hα0 : α ≠ 0 := fun h => by simp [h] at hα
  rw [integral_cpow_mul_exp_neg_mul_eq_cpow hα hw, Complex.cpow_def_of_ne_zero hα0,
    mul_comm (Complex.exp _) (Complex.Gamma w)]
  congr 2
  ring

end GammaRate

end

section IteratedDerivBounds

set_option autoImplicit false

open Set

namespace DerivBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {β : Type*} [Fintype β] {ι : Type*}

private noncomputable def coordL (b : Module.Basis β ℝ X) (k : β) : X →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (b.coord k)

omit [Fintype β] in
private theorem coordL_apply (b : Module.Basis β ℝ X) (k : β) (v : X) : coordL b k v = b.repr v k := by
  simp [coordL]

private theorem fderiv_eq_sum (b : Module.Basis β ℝ X) (f : X → ℂ) (y : X) :
    fderiv ℝ f y =
      ∑ k, ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k) (fderiv ℝ f y (b k)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, coordL_apply]
  conv_lhs => rw [← b.sum_repr v, map_sum]
  simp only [map_smul]

private theorem iteratedFDerivWithin_bound_of_closed (b : Module.Basis β ℝ X) (s : Set X) (hs : IsOpen s)
    (pt : ι → X) (hpt : ∀ i, pt i ∈ s) (φ : ℕ → ι → ℝ) (hφ0 : ∀ m i, 0 ≤ φ m i) (hφ : Monotone φ)
    (𝓟 : (X → ℂ) → Prop) (hsmooth : ∀ f, 𝓟 f → ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (hderiv : ∀ f, 𝓟 f → ∀ k : β, 𝓟 (fun x => fderiv ℝ f x (b k)))
    (hbound : ∀ f, 𝓟 f → ∃ (C : ℝ) (m : ℕ), ∀ i, ‖f (pt i)‖ ≤ C * φ m i) :
    ∀ (j : ℕ) (f : X → ℂ), 𝓟 f →
      ∃ (C : ℝ) (m : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * φ m i := by
  suffices H : ∀ (j : ℕ) (f : X → ℂ), 𝓟 f → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
      ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * φ m i by
    intro j f hf
    obtain ⟨C, m, -, h⟩ := H j f hf
    exact ⟨C, m, h⟩
  have hsU : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  intro j
  induction j with
  | zero =>
    intro f hf
    obtain ⟨C, m, h⟩ := hbound f hf
    refine ⟨max C 0, m, le_max_right _ _, fun i => ?_⟩
    rw [norm_iteratedFDerivWithin_zero]
    exact (h i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hφ0 m i))
  | succ j ih =>
    intro f hf
    choose C m hC0 hCm using fun k : β => ih _ (hderiv f hf k)
    refine ⟨∑ k, ‖ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k)‖ * C k, Finset.univ.sup m,
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (norm_nonneg (ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k))) (hC0 k), fun i => ?_⟩
    have hx : pt i ∈ s := hpt i
    have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have hg : ∀ k : β, ContDiffWithinAt ℝ j (fun x => fderiv ℝ f x (b k)) s (pt i) := fun k =>
      ((hsmooth _ (hderiv f hf k)).contDiffWithinAt hx).of_le hj
    have hEq : EqOn (fderivWithin ℝ f s)
        (∑ k, ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k) ∘ fun x => fderiv ℝ f x (b k)) s := by
      intro y hy
      rw [fderivWithin_of_isOpen hs hy, fderiv_eq_sum b f y]
      simp only [Finset.sum_apply, Function.comp_apply]
    rw [← norm_iteratedFDerivWithin_fderivWithin hsU hx, iteratedFDerivWithin_congr hEq hx,
      iteratedFDerivWithin_sum_apply hsU hx
        (fun k _ => (ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k)).contDiff.comp_contDiffWithinAt (hg k))]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [(ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k)).iteratedFDerivWithin_comp_left (hg k) hsU hx
      le_rfl, mul_assoc]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖iteratedFDerivWithin ℝ j (fun x => fderiv ℝ f x (b k)) s (pt i)‖
        ≤ C k * φ (m k) i := hCm k i
      _ ≤ C k * φ (Finset.univ.sup m) i :=
        mul_le_mul_of_nonneg_left (hφ (Finset.le_sup (f := m) (Finset.mem_univ k)) i) (hC0 k)

end DerivBounds

end IteratedDerivBounds

section DecayScaleBounds

set_option autoImplicit false

namespace DecayScale

private theorem scale_nonneg (m : ℕ) (y : ℝ) :
    0 ≤ (|y| + |y|⁻¹ + 1) ^ m * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|)) := by
  positivity

private theorem one_le_base (y : ℝ) : (1 : ℝ) ≤ |y| + |y|⁻¹ + 1 := by
  have h : 0 ≤ |y| + |y|⁻¹ := by positivity
  linarith

private theorem scale_mono (y : ℝ) :
    Monotone fun m : ℕ =>
      (|y| + |y|⁻¹ + 1) ^ m * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|)) := by
  intro m n hmn
  show (|y| + |y|⁻¹ + 1) ^ m * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|)) ≤
    (|y| + |y|⁻¹ + 1) ^ n * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_base y) hmn) (by positivity)) (by positivity)

private theorem scale_monotone_family {ι : Type*} (yy : ι → ℝ) :
    Monotone fun (m : ℕ) (i : ι) =>
      (|yy i| + |yy i|⁻¹ + 1) ^ m * |yy i| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |yy i|)) :=
  fun _ _ hmn => Pi.le_def.mpr fun i => scale_mono (yy i) hmn

private theorem scale_le_of_abs_le_one (m : ℕ) {y : ℝ} (hy : y ≠ 0) (hy1 : |y| ≤ 1) :
    (|y| + |y|⁻¹ + 1) ^ m * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|)) ≤
      (3 : ℝ) ^ m * |y| ^ (-(m : ℝ)) := by
  have hpos : 0 < |y| := abs_pos.mpr hy
  have hinv : 1 ≤ |y|⁻¹ := (one_le_inv₀ hpos).mpr hy1
  have hbase : |y| + |y|⁻¹ + 1 ≤ 3 * |y|⁻¹ := by linarith
  have hpow : (|y| + |y|⁻¹ + 1) ^ m ≤ (3 * |y|⁻¹) ^ m := pow_le_pow_left₀ (by positivity) hbase m
  have hr : |y| ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hpos.le hy1 (by norm_num)
  have he : Real.exp (-(2 * Real.pi * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hrhs : (3 : ℝ) ^ m * |y| ^ (-(m : ℝ)) = (3 * |y|⁻¹) ^ m := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, mul_pow, inv_pow]
  rw [hrhs]
  calc (|y| + |y|⁻¹ + 1) ^ m * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|))
      ≤ (3 * |y|⁻¹) ^ m * 1 * 1 := by gcongr
    _ = (3 * |y|⁻¹) ^ m := by ring

private theorem exists_scale_le_of_one_le_abs (m N : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ |y| →
      (|y| + |y|⁻¹ + 1) ^ m * |y| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |y|)) ≤
        C * |y| ^ (-(N : ℝ)) := by
  refine ⟨(3 : ℝ) ^ m * (((m + 2 + N).factorial : ℝ) / (2 * Real.pi) ^ (m + 2 + N)), fun y hy => ?_⟩
  have hpos : 0 < |y| := by linarith
  have hinv : |y|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
  have hbase : |y| + |y|⁻¹ + 1 ≤ 3 * |y| := by linarith
  have hpow : (|y| + |y|⁻¹ + 1) ^ m ≤ (3 * |y|) ^ m := pow_le_pow_left₀ (by positivity) hbase m
  have hr : |y| ^ (3 / 2 : ℝ) ≤ |y| ^ 2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have hx : 0 < 2 * Real.pi * |y| := by positivity
  have hexp : (2 * Real.pi * |y|) ^ (m + 2 + N) / ((m + 2 + N).factorial : ℝ) ≤
      Real.exp (2 * Real.pi * |y|) :=
    Real.pow_div_factorial_le_exp _ hx.le (m + 2 + N)
  have hE : Real.exp (-(2 * Real.pi * |y|)) ≤
      ((m + 2 + N).factorial : ℝ) / (2 * Real.pi * |y|) ^ (m + 2 + N) := by
    rw [Real.exp_neg, ← inv_div]
    exact inv_anti₀ (by positivity) hexp
  have hy0 : |y| ≠ 0 := hpos.ne'
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hmain : (3 * |y|) ^ m * |y| ^ 2 *
        (((m + 2 + N).factorial : ℝ) / (2 * Real.pi * |y|) ^ (m + 2 + N)) =
      (3 : ℝ) ^ m * (((m + 2 + N).factorial : ℝ) / (2 * Real.pi) ^ (m + 2 + N)) * |y| ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    field_simp
    ring
  rw [← hmain]
  gcongr

end DecayScale

end DecayScaleBounds

namespace DiscreteFamily

p2m_open "LanglandsTunnell.Converse.ArchR"

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

private def P (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) : RealArchParam := RealArchParam.discrete u₀ k₀ hk

section

variable {u₀ : ℂ} {k₀ : ℕ} {hk : 1 ≤ k₀}

private def nsq (g : M₂) : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

private def iy (g : M₂) : ℝ := g.det / nsq g

private def ix (g : M₂) : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / nsq g

private def kap (g : M₂) : ℂ := ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) / (Real.sqrt (nsq g) : ℂ)

private def pexp (k₀ : ℕ) : ℝ := (k₀ : ℝ) / 2 + 1

private def prof (k₀ : ℕ) (y : ℝ) : ℝ := y ^ pexp k₀ * Real.exp (-(2 * Real.pi * y))

private def detPow (u₀ : ℂ) (g : M₂) : ℂ := Complex.exp (u₀ * (Real.log g.det : ℂ))

private def _root_.LanglandsTunnell.Converse.DiscreteFamily.W (u₀ : ℂ) (k₀ : ℕ) (g : M₂) : ℂ :=
  if 0 < g.det then
    psi (ix g) * (prof k₀ (iy g) : ℂ) * kap g ^ (k₀ + 1) * (Real.sqrt (nsq g) : ℂ) * detPow u₀ g
  else 0

p2m_export "LanglandsTunnell.Converse.DiscreteFamily" "W"
private theorem det_eq (g : M₂) : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

private theorem nsq_nonneg (g : M₂) : 0 ≤ nsq g := by unfold nsq; positivity

private theorem nsq_pos_of_det_ne_zero {g : M₂} (h : g.det ≠ 0) : 0 < nsq g := by
  rcases (nsq_nonneg g).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have h0 : g 1 0 = 0 ∧ g 1 1 = 0 := by
      have := heq.symm
      unfold nsq at this
      constructor <;> nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply h
    rw [det_eq, h0.1, h0.2]; ring

private theorem unip_mul_apply (x : ℝ) (g : M₂) :
    (unip x * g) 0 0 = g 0 0 + x * g 1 0 ∧ (unip x * g) 0 1 = g 0 1 + x * g 1 1 ∧
    (unip x * g) 1 0 = g 1 0 ∧ (unip x * g) 1 1 = g 1 1 := by
  simp [unip, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_unip_mul (x : ℝ) (g : M₂) : (unip x * g).det = g.det := by
  rw [Matrix.det_mul]; simp [unip, Matrix.det_fin_two]

private theorem nsq_unip_mul (x : ℝ) (g : M₂) : nsq (unip x * g) = nsq g := by
  obtain ⟨-, -, h10, h11⟩ := unip_mul_apply x g
  simp only [nsq, h10, h11]

private theorem iy_unip_mul (x : ℝ) (g : M₂) : iy (unip x * g) = iy g := by
  simp only [iy, det_unip_mul, nsq_unip_mul]

private theorem kap_unip_mul (x : ℝ) (g : M₂) : kap (unip x * g) = kap g := by
  obtain ⟨-, -, h10, h11⟩ := unip_mul_apply x g
  simp only [kap, h10, h11, nsq_unip_mul]

private theorem ix_unip_mul (x : ℝ) {g : M₂} (hg : g.det ≠ 0) : ix (unip x * g) = ix g + x := by
  obtain ⟨h00, h01, h10, h11⟩ := unip_mul_apply x g
  have hn : nsq g ≠ 0 := (nsq_pos_of_det_ne_zero hg).ne'
  simp only [ix, h00, h01, h10, h11, nsq_unip_mul]
  field_simp
  simp only [nsq]; ring

private theorem psi_add (x x' : ℝ) : psi (x + x') = psi x * psi x' := by
  simp only [psi, ← Complex.exp_add]; congr 1; push_cast; ring

private theorem W_unip_mul (x : ℝ) (g : M₂) : W u₀ k₀ (unip x * g) = psi x * W u₀ k₀ g := by
  unfold W detPow
  rw [det_unip_mul]
  split_ifs with h
  · rw [ix_unip_mul x h.ne', iy_unip_mul, kap_unip_mul, nsq_unip_mul, psi_add]; ring
  · simp

private theorem smul_apply' (z : ℝ) (g : M₂) (i j : Fin 2) : (z • g) i j = z * g i j := rfl

private theorem det_smul' (z : ℝ) (g : M₂) : (z • g).det = z ^ 2 * g.det := by
  rw [Matrix.det_smul]; simp

private theorem nsq_smul (z : ℝ) (g : M₂) : nsq (z • g) = z ^ 2 * nsq g := by
  simp only [nsq, smul_apply']; ring

private theorem iy_smul {z : ℝ} (hz : z ≠ 0) (g : M₂) : iy (z • g) = iy g := by
  simp only [iy, det_smul', nsq_smul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hz)

private theorem ix_smul {z : ℝ} (hz : z ≠ 0) (g : M₂) : ix (z • g) = ix g := by
  simp only [ix, smul_apply', nsq_smul]
  rw [show z * g 0 0 * (z * g 1 0) + z * g 0 1 * (z * g 1 1) = z ^ 2 * (g 0 0 * g 1 0 + g 0 1 * g 1 1) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hz)

private theorem sqrt_nsq_smul (z : ℝ) (g : M₂) : Real.sqrt (nsq (z • g)) = |z| * Real.sqrt (nsq g) := by
  rw [nsq_smul, Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq_eq_abs]

private theorem kap_smul {z : ℝ} (hz : z ≠ 0) (g : M₂) : kap (z • g) = ((z : ℂ) / ((|z| : ℝ) : ℂ)) * kap g := by
  simp only [kap, smul_apply', sqrt_nsq_smul]
  have habs : ((|z| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hz).ne'
  by_cases hs : (Real.sqrt (nsq g) : ℂ) = 0
  · simp [hs]
  · push_cast
    field_simp

private theorem sign_pow_of_even {z : ℝ} (hz : z ≠ 0) (h : (k₀ : ZMod 2) + 1 = 0) :
    ((z : ℂ) / ((|z| : ℝ) : ℂ)) ^ (k₀ + 1) = 1 := by
  have he : Even (k₀ + 1) := by rw [← ZMod.natCast_eq_zero_iff_even]; exact_mod_cast h
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · rw [abs_of_neg hneg]; push_cast
    rw [div_neg, div_self (by exact_mod_cast hneg.ne), he.neg_one_pow]
  · rw [abs_of_pos hpos, div_self (by exact_mod_cast hpos.ne'), one_pow]

private theorem sign_pow_of_odd {z : ℝ} (hz : z ≠ 0) (h : ¬ (k₀ : ZMod 2) + 1 = 0) :
    ((z : ℂ) / ((|z| : ℝ) : ℂ)) ^ (k₀ + 1) = ((SignType.sign z : ℝ) : ℂ) := by
  have ho : Odd (k₀ + 1) := by
    rcases Nat.even_or_odd (k₀ + 1) with he | ho
    · exact absurd (by rw [← ZMod.natCast_eq_zero_iff_even] at he; exact_mod_cast he) h
    · exact ho
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · rw [abs_of_neg hneg, sign_neg hneg]; push_cast
    rw [div_neg, div_self (by exact_mod_cast hneg.ne), ho.neg_one_pow]; simp
  · rw [abs_of_pos hpos, sign_pos hpos, div_self (by exact_mod_cast hpos.ne'), one_pow]; simp

private theorem detPow_smul {z : ℝ} (hz : z ≠ 0) {g : M₂} (hg : 0 < g.det) :
    detPow u₀ (z • g) = Complex.exp (2 * u₀ * (Real.log |z| : ℂ)) * detPow u₀ g := by
  unfold detPow
  rw [det_smul', ← Complex.exp_add]
  congr 1
  rw [Real.log_mul (pow_ne_zero 2 hz) hg.ne', Real.log_pow, ← Real.log_abs]
  push_cast; ring

private theorem abs_cpow_eq {z : ℝ} (hz : z ≠ 0) :
    ((|z| : ℝ) : ℂ) ^ (2 * u₀) = Complex.exp (2 * u₀ * (Real.log |z| : ℂ)) := by
  have h0 : ((|z| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hz).ne'
  rw [Complex.cpow_def_of_ne_zero h0, Complex.ofReal_log (abs_nonneg z), mul_comm]

private theorem W_smul {z : ℝ} (hz : z ≠ 0) (g : M₂) :
    W u₀ k₀ (z • g) = centralChar (P u₀ k₀ hk) z * ((|z| : ℝ) : ℂ) * W u₀ k₀ g := by
  unfold W
  have hpos : (0 < (z • g).det ↔ 0 < g.det) := by
    rw [det_smul']
    exact mul_pos_iff_of_pos_left (by positivity)
  by_cases h : 0 < g.det
  · rw [if_pos (hpos.mpr h), if_pos h, ix_smul hz, iy_smul hz, kap_smul hz, mul_pow, sqrt_nsq_smul,
      detPow_smul hz h]
    simp only [centralChar, P, quasiChar, RealArchParam.centralExponent, RealArchParam.centralSign, abs_cpow_eq hz]
    split_ifs with hpar
    · rw [sign_pow_of_even hz hpar]; push_cast; ring
    · rw [sign_pow_of_odd hz hpar]; push_cast; ring
  · rw [if_neg (fun h' => h (hpos.mp h')), if_neg h, mul_zero]

private def posSet : Set (Fin 2 → Fin 2 → ℝ) := {m | 0 < (Matrix.of m).det}

private def negSet : Set (Fin 2 → Fin 2 → ℝ) := {m | (Matrix.of m).det < 0}

private theorem contDiff_coord (i j : Fin 2) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun m : Fin 2 → Fin 2 → ℝ => m i j) :=
  (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)

private theorem contDiff_detCoord {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun m : Fin 2 → Fin 2 → ℝ => (Matrix.of m).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((contDiff_coord 0 0).mul (contDiff_coord 1 1)).sub ((contDiff_coord 0 1).mul (contDiff_coord 1 0))

private theorem contDiff_nsqCoord {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun m : Fin 2 → Fin 2 → ℝ => nsq (Matrix.of m)) := by
  simp only [nsq, Matrix.of_apply]
  exact ((contDiff_coord 1 0).pow 2).add ((contDiff_coord 1 1).pow 2)

private theorem isOpen_posSet : IsOpen posSet := isOpen_lt continuous_const (contDiff_detCoord (n := 1)).continuous
private theorem isOpen_negSet : IsOpen negSet := isOpen_lt (contDiff_detCoord (n := 1)).continuous continuous_const

private theorem glSet_eq : glSet = posSet ∪ negSet := by
  ext m
  simp only [glSet, posSet, negSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact h.ne'
    · exact h.ne

private theorem contDiffOn_formula {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ =>
      psi (ix (Matrix.of m)) * (prof k₀ (iy (Matrix.of m)) : ℂ) * kap (Matrix.of m) ^ (k₀ + 1) *
        (Real.sqrt (nsq (Matrix.of m)) : ℂ) * detPow u₀ (Matrix.of m)) posSet := by
  have hnsq : ∀ m ∈ posSet, nsq (Matrix.of m) ≠ 0 := fun m hm =>
    (nsq_pos_of_det_ne_zero (show (Matrix.of m).det ≠ 0 from hm.ne')).ne'
  have hN : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => nsq (Matrix.of m)) posSet :=
    contDiff_nsqCoord.contDiffOn
  have hsqrt : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => Real.sqrt (nsq (Matrix.of m))) posSet :=
    hN.sqrt hnsq
  have hsqrt_ne : ∀ m ∈ posSet, Real.sqrt (nsq (Matrix.of m)) ≠ 0 := fun m hm =>
    (Real.sqrt_pos.mpr (lt_of_le_of_ne (nsq_nonneg _) (Ne.symm (hnsq m hm)))).ne'
  have hsqrtC : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => (Real.sqrt (nsq (Matrix.of m)) : ℂ)) posSet :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt
  have hnum : ContDiffOn ℝ n
      (fun m : Fin 2 → Fin 2 → ℝ => (Matrix.of m) 0 0 * (Matrix.of m) 1 0 + (Matrix.of m) 0 1 * (Matrix.of m) 1 1)
      posSet := by
    simp only [Matrix.of_apply]
    exact (((contDiff_coord 0 0).mul (contDiff_coord 1 0)).add
      ((contDiff_coord 0 1).mul (contDiff_coord 1 1))).contDiffOn
  have hix : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => ix (Matrix.of m)) posSet := hnum.div hN hnsq
  have hiy : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => iy (Matrix.of m)) posSet :=
    contDiff_detCoord.contDiffOn.div hN hnsq
  have hiy_ne : ∀ m ∈ posSet, iy (Matrix.of m) ≠ 0 := fun m hm =>
    (div_pos hm (lt_of_le_of_ne (nsq_nonneg _) (Ne.symm (hnsq m hm)))).ne'
  have hixC : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => (ix (Matrix.of m) : ℂ)) posSet :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hix
  have hpsi : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => psi (ix (Matrix.of m))) posSet := by
    have hlin : ContDiffOn ℝ n
        (fun m : Fin 2 → Fin 2 → ℝ => 2 * (Real.pi : ℂ) * I * (ix (Matrix.of m) : ℂ)) posSet :=
      contDiffOn_const.mul hixC
    exact Complex.contDiff_exp.comp_contDiffOn hlin
  have hprofR : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => prof k₀ (iy (Matrix.of m))) posSet := by
    have hexp : ContDiffOn ℝ n
        (fun m : Fin 2 → Fin 2 → ℝ => Real.exp (-(2 * Real.pi * iy (Matrix.of m)))) posSet :=
      Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hiy).neg
    exact (hiy.rpow_const_of_ne hiy_ne).mul hexp
  have hprof : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => (prof k₀ (iy (Matrix.of m)) : ℂ)) posSet :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hprofR
  have hd : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => ((Matrix.of m) 1 1 : ℂ)) posSet := by
    simp only [Matrix.of_apply]
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_coord 1 1)).contDiffOn
  have hc : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => ((Matrix.of m) 1 0 : ℂ)) posSet := by
    simp only [Matrix.of_apply]
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_coord 1 0)).contDiffOn
  have hkap : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => kap (Matrix.of m)) posSet := by
    have hnumC : ContDiffOn ℝ n
        (fun m : Fin 2 → Fin 2 → ℝ => ((Matrix.of m) 1 1 : ℂ) - ((Matrix.of m) 1 0 : ℂ) * I) posSet :=
      hd.sub (hc.mul contDiffOn_const)
    have hk : (fun m : Fin 2 → Fin 2 → ℝ => kap (Matrix.of m)) = fun m : Fin 2 → Fin 2 → ℝ =>
        (((Matrix.of m) 1 1 : ℂ) - ((Matrix.of m) 1 0 : ℂ) * I) * ((Real.sqrt (nsq (Matrix.of m)) : ℂ))⁻¹ := by
      funext m; simp only [kap, div_eq_mul_inv]
    rw [hk]
    exact hnumC.mul (hsqrtC.inv fun m hm => by exact_mod_cast hsqrt_ne m hm)
  have hdetPow : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => detPow u₀ (Matrix.of m)) posSet := by
    have hlog : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => Real.log (Matrix.of m).det) posSet :=
      contDiff_detCoord.contDiffOn.log fun m hm => (show (0 : ℝ) < (Matrix.of m).det from hm).ne'
    have hlin : ContDiffOn ℝ n (fun m : Fin 2 → Fin 2 → ℝ => u₀ * (Real.log (Matrix.of m).det : ℂ)) posSet :=
      contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog)
    exact Complex.contDiff_exp.comp_contDiffOn hlin
  exact (((hpsi.mul hprof).mul (hkap.pow (k₀ + 1))).mul hsqrtC).mul hdetPow

private theorem contDiffOn_asPi_W {n : WithTop ℕ∞} : ContDiffOn ℝ n (asPi (W u₀ k₀)) glSet := by
  rw [glSet_eq]
  refine contDiffOn_of_locally_contDiffOn fun m hm => ?_
  rcases hm with hm | hm
  · refine ⟨posSet, isOpen_posSet, hm, ?_⟩
    refine ((contDiffOn_formula (u₀ := u₀) (k₀ := k₀)).mono Set.inter_subset_right).congr fun m' hm' => ?_
    simp only [asPi, W, if_pos (show 0 < (Matrix.of m').det from hm'.2)]
  · refine ⟨negSet, isOpen_negSet, hm, ?_⟩
    refine (contDiffOn_const (c := (0 : ℂ))).congr fun m' hm' => ?_
    simp only [asPi, W, if_neg (not_lt.mpr (le_of_lt (show (Matrix.of m').det < 0 from hm'.2)))]

private def sgn (g : M₂) : ℝ := if 0 < g.det then 1 else -1

private def chiSign (a : ZMod 2) (g : M₂) : ℂ := if a = 0 then 1 else (sgn g : ℂ)

private def rate (g : M₂) : ℂ := 2 * (Real.pi : ℂ) * ((sgn g : ℂ) * ((iy g : ℂ) - (ix g : ℂ) * I))

private def detAbsPow (u₀ : ℂ) (g : M₂) : ℂ := Complex.exp (u₀ * (Real.log |g.det| : ℂ))

private def zconst (u₀ : ℂ) (k₀ : ℕ) (a : ZMod 2) (g : M₂) : ℂ :=
  chiSign a g * ((|iy g| ^ pexp k₀ : ℝ) : ℂ) * kap g ^ (k₀ + 1) * (Real.sqrt (nsq g) : ℂ) * detAbsPow u₀ g

private def shift (u₀ : ℂ) (k₀ : ℕ) : ℂ := u₀ + (k₀ : ℂ) / 2

private def wvar (u₀ : ℂ) (k₀ : ℕ) (u s : ℂ) : ℂ := s + u + shift u₀ k₀

private def zetaEnt (u₀ : ℂ) (k₀ : ℕ) (g : M₂) (u : ℂ) (a : ZMod 2) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * zconst u₀ k₀ a g *
    Complex.exp (wvar u₀ k₀ u s * (Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g)))

private theorem sgn_sq (g : M₂) : sgn g ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num

private theorem sgn_mul_det_pos {g : M₂} (h : g.det ≠ 0) : 0 < sgn g * g.det := by
  unfold sgn; split_ifs with hpos
  · simpa using hpos
  · have : g.det < 0 := lt_of_le_of_ne (not_lt.mp hpos) h
    nlinarith

private theorem sgn_mul_iy_pos {g : M₂} (h : g.det ≠ 0) : 0 < sgn g * iy g := by
  unfold iy; rw [mul_div_assoc'] ; exact div_pos (sgn_mul_det_pos h) (nsq_pos_of_det_ne_zero h)

private theorem abs_iy {g : M₂} (h : g.det ≠ 0) : |iy g| = sgn g * iy g := by
  have hs := sgn_mul_iy_pos h
  unfold sgn at hs ⊢
  split_ifs at hs ⊢ with hpos
  · simp only [one_mul] at hs ⊢; exact abs_of_pos hs
  · simp only [neg_one_mul] at hs ⊢; exact abs_of_neg (by linarith)

private theorem rate_re {g : M₂} : (rate g).re = 2 * Real.pi * (sgn g * iy g) := by
  simp [rate]

private theorem rate_re_pos {g : M₂} (h : g.det ≠ 0) : 0 < (rate g).re := by
  rw [rate_re]; exact mul_pos (by positivity) (sgn_mul_iy_pos h)

private theorem rate_ne_zero {g : M₂} (h : g.det ≠ 0) : rate g ≠ 0 := fun h0 => by
  have := rate_re_pos h; rw [h0] at this; simp at this

private theorem zetaEnt_differentiable (g : M₂) (u : ℂ) (a : ZMod 2) : Differentiable ℂ (zetaEnt u₀ k₀ g u a) := by
  unfold zetaEnt wvar
  fun_prop

private theorem diagOne_mul_apply (τ : ℝ) (g : M₂) :
    (diagOne τ * g) 0 0 = τ * g 0 0 ∧ (diagOne τ * g) 0 1 = τ * g 0 1 ∧
    (diagOne τ * g) 1 0 = g 1 0 ∧ (diagOne τ * g) 1 1 = g 1 1 := by
  simp [diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_diagOne_mul (τ : ℝ) (g : M₂) : (diagOne τ * g).det = τ * g.det := by
  rw [Matrix.det_mul]; simp [diagOne, Matrix.det_fin_two]

private theorem nsq_diagOne_mul (τ : ℝ) (g : M₂) : nsq (diagOne τ * g) = nsq g := by
  obtain ⟨-, -, h10, h11⟩ := diagOne_mul_apply τ g
  simp only [nsq, h10, h11]

private theorem kap_diagOne_mul (τ : ℝ) (g : M₂) : kap (diagOne τ * g) = kap g := by
  obtain ⟨-, -, h10, h11⟩ := diagOne_mul_apply τ g
  simp only [kap, h10, h11, nsq_diagOne_mul]

private theorem iy_diagOne_mul (τ : ℝ) (g : M₂) : iy (diagOne τ * g) = τ * iy g := by
  simp only [iy, det_diagOne_mul, nsq_diagOne_mul, mul_div_assoc]

private theorem ix_diagOne_mul (τ : ℝ) (g : M₂) : ix (diagOne τ * g) = τ * ix g := by
  obtain ⟨h00, h01, h10, h11⟩ := diagOne_mul_apply τ g
  simp only [ix, h00, h01, h10, h11, nsq_diagOne_mul]
  ring

private theorem zetaIntegrand_eq_zero_of_nonpos {g : M₂} (u : ℂ) (a : ZMod 2) (s : ℂ) {τ : ℝ}
    (hτ : sgn g * τ ≤ 0) : zetaIntegrand (W u₀ k₀) g u a s τ = 0 := by
  have hW : W u₀ k₀ (diagOne τ * g) = 0 := by
    unfold W
    rw [if_neg]
    rw [det_diagOne_mul]
    intro hpos
    unfold sgn at hτ
    split_ifs at hτ with hd
    · nlinarith [mul_pos_iff.mp hpos]
    · have hd' : g.det < 0 ∨ g.det = 0 := lt_or_eq_of_le (not_lt.mp hd)
      rcases hd' with hd' | hd'
      · nlinarith [mul_pos_iff.mp hpos]
      · simp [hd'] at hpos
  simp [zetaIntegrand, hW]

private theorem zetaIntegrand_eq_of_pos {g : M₂} (hg : g.det ≠ 0) (u : ℂ) (a : ZMod 2) (s : ℂ) {τ : ℝ}
    (hτ : 0 < sgn g * τ) :
    zetaIntegrand (W u₀ k₀) g u a s τ =
      zconst u₀ k₀ a g * (((sgn g * τ : ℝ) : ℂ) ^ (wvar u₀ k₀ u s - 1) *
        Complex.exp (-(rate g * ((sgn g * τ : ℝ) : ℂ)))) := by

  have hτdet : 0 < τ * g.det := by
    have h1 := sgn_mul_det_pos hg
    have h2 := sgn_sq g
    nlinarith [mul_pos hτ h1]
  have hcase : (sgn g = 1 ∧ 0 < τ) ∨ (sgn g = -1 ∧ τ < 0) := by
    unfold sgn at hτ ⊢
    split_ifs at hτ ⊢ with hd
    · exact Or.inl ⟨rfl, by simpa using hτ⟩
    · exact Or.inr ⟨rfl, by linarith⟩
  have habsτ' : |τ| = sgn g * τ := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, one_mul]; exact abs_of_pos h2
    · rw [h1, neg_one_mul]; exact abs_of_neg h2
  have hsignτ' : (SignType.sign τ : ℝ) = sgn g := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; simp [sign_pos h2]
    · rw [h1]; simp [sign_neg h2]
  set ρ : ℝ := sgn g * τ with hρ
  have hρpos : 0 < ρ := hτ
  have hsg2 : sgn g * sgn g = 1 := by have := sgn_sq g; nlinarith [this]
  have habsτ : |τ| = ρ := habsτ'
  have hτiy : τ * iy g = ρ * |iy g| := by
    rw [abs_iy hg, hρ]; ring_nf; rw [show sgn g ^ 2 = 1 from sgn_sq g]; ring
  have hτdet' : τ * g.det = ρ * |g.det| := by
    have hsd : |g.det| = sgn g * g.det := by
      unfold sgn; split_ifs with hpos
      · rw [one_mul]; exact abs_of_pos hpos
      · rw [neg_one_mul]; exact abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hg)
    rw [hsd, hρ]; ring_nf; rw [show sgn g ^ 2 = 1 from sgn_sq g]; ring
  have hsignτ : ((SignType.sign τ : ℝ) : ℂ) = (sgn g : ℂ) := by exact_mod_cast hsignτ'
  have hdet0 : 0 < |g.det| := abs_pos.mpr hg

  have hdetPow : detPow u₀ (diagOne τ * g) = (ρ : ℂ) ^ u₀ * detAbsPow u₀ g := by
    unfold detPow detAbsPow
    rw [det_diagOne_mul, hτdet', Real.log_mul hρpos.ne' hdet0.ne', Complex.cpow_def_of_ne_zero
      (by exact_mod_cast hρpos.ne'), ← Complex.ofReal_log hρpos.le, ← Complex.exp_add]
    congr 1; push_cast; ring

  have hWd : W u₀ k₀ (diagOne τ * g) =
      psi (τ * ix g) * (prof k₀ (ρ * |iy g|) : ℂ) * kap g ^ (k₀ + 1) * (Real.sqrt (nsq g) : ℂ) *
        ((ρ : ℂ) ^ u₀ * detAbsPow u₀ g) := by
    unfold W
    rw [if_pos (by rw [det_diagOne_mul]; exact hτdet), ix_diagOne_mul, iy_diagOne_mul, kap_diagOne_mul,
      nsq_diagOne_mul, hτiy, hdetPow]
  unfold zetaIntegrand
  rw [hWd]
  unfold quasiChar zconst chiSign prof psi wvar rate
  rw [habsτ]

  have hchi : (if a = 0 then (1 : ℂ) else ((SignType.sign τ : ℝ) : ℂ)) = (if a = 0 then 1 else (sgn g : ℂ)) := by
    rw [hsignτ]
  rw [hchi]

  have hiy0 : 0 < |iy g| := abs_pos.mpr (by
    intro h0; have := sgn_mul_iy_pos hg; rw [h0, mul_zero] at this; exact lt_irrefl _ this)
  have hrpow : ((ρ * |iy g|) ^ pexp k₀ : ℝ) = ρ ^ pexp k₀ * |iy g| ^ pexp k₀ :=
    Real.mul_rpow hρpos.le hiy0.le
  rw [hrpow]
  push_cast

  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
  have hpowp : ((ρ ^ pexp k₀ : ℝ) : ℂ) = (ρ : ℂ) ^ ((pexp k₀ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hρpos.le]
  rw [hpowp]
  have hcombine : (ρ : ℂ) ^ ((pexp k₀ : ℝ) : ℂ) * (ρ : ℂ) ^ u₀ * (ρ : ℂ) ^ u * (ρ : ℂ) ^ (s - 1) * ((ρ : ℂ))⁻¹ =
      (ρ : ℂ) ^ (s + u + shift u₀ k₀ - 1) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hρC, ← Complex.cpow_add _ _ hρC,
      ← Complex.cpow_add _ _ hρC, ← Complex.cpow_add _ _ hρC]
    congr 1
    unfold pexp shift; push_cast; ring

  have hexp : Complex.exp (2 * (Real.pi : ℂ) * I * ((τ * ix g : ℝ) : ℂ)) *
      Complex.exp (-(2 * Real.pi * (ρ * |iy g|)) : ℝ) =
      Complex.exp (-(2 * (Real.pi : ℂ) * ((sgn g : ℂ) * ((iy g : ℂ) - (ix g : ℂ) * I)) * (ρ : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    have hτC : (τ : ℂ) = (sgn g : ℂ) * (ρ : ℂ) := by
      rw [hρ]; push_cast; rw [← mul_assoc, show (sgn g : ℂ) * (sgn g : ℂ) = 1 by exact_mod_cast hsg2, one_mul]
    have habsiyC : ((|iy g| : ℝ) : ℂ) = (sgn g : ℂ) * (iy g : ℂ) := by rw [abs_iy hg]; push_cast; ring
    push_cast
    rw [hτC, habsiyC]
    ring

  calc _ = ((if a = 0 then (1 : ℂ) else (sgn g : ℂ)) * ((|iy g| ^ pexp k₀ : ℝ) : ℂ) * kap g ^ (k₀ + 1) *
          (Real.sqrt (nsq g) : ℂ) * detAbsPow u₀ g) *
        (((ρ : ℂ) ^ ((pexp k₀ : ℝ) : ℂ) * (ρ : ℂ) ^ u₀ * (ρ : ℂ) ^ u * (ρ : ℂ) ^ (s - 1) * ((ρ : ℂ))⁻¹) *
          (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ * ix g : ℝ) : ℂ)) *
            Complex.exp (-(2 * Real.pi * (ρ * |iy g|)) : ℝ))) := by push_cast; ring
    _ = _ := by rw [hcombine, hexp]

private theorem wvar_re {u s : ℂ} : (wvar u₀ k₀ u s).re = s.re + u.re + (shift u₀ k₀).re := by
  simp [wvar]

private theorem wvar_re_pos {u s : ℂ} (h : -(shift u₀ k₀).re < s.re + u.re) : 0 < (wvar u₀ k₀ u s).re := by
  rw [wvar_re]; linarith

private def halfLine (u₀ : ℂ) (k₀ : ℕ) (g : M₂) (u : ℂ) (a : ZMod 2) (s : ℂ) (ρ : ℝ) : ℂ :=
  if 0 < ρ then zconst u₀ k₀ a g * ((ρ : ℂ) ^ (wvar u₀ k₀ u s - 1) * Complex.exp (-(rate g * (ρ : ℂ)))) else 0

private theorem zetaIntegrand_eq_halfLine {g : M₂} (hg : g.det ≠ 0) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    zetaIntegrand (W u₀ k₀) g u a s = fun τ => halfLine u₀ k₀ g u a s (sgn g * τ) := by
  funext τ
  unfold halfLine
  split_ifs with h
  · exact zetaIntegrand_eq_of_pos hg u a s h
  · exact zetaIntegrand_eq_zero_of_nonpos u a s (not_lt.mp h)

private theorem halfLine_eqOn (g : M₂) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    Set.EqOn (fun ρ : ℝ => zconst u₀ k₀ a g * ((ρ : ℂ) ^ (wvar u₀ k₀ u s - 1) * Complex.exp (-(rate g * (ρ : ℂ)))))
      (halfLine u₀ k₀ g u a s) (Set.Ioi 0) := by
  intro ρ hρ
  simp only [halfLine, if_pos (Set.mem_Ioi.mp hρ)]

private theorem halfLine_integrableOn {g : M₂} (hg : g.det ≠ 0) {u s : ℂ} (hw : 0 < (wvar u₀ k₀ u s).re) (a : ZMod 2) :
    MeasureTheory.IntegrableOn (halfLine u₀ k₀ g u a s) (Set.Ioi 0) := by
  have h : MeasureTheory.IntegrableOn
      (fun ρ : ℝ => zconst u₀ k₀ a g * ((ρ : ℂ) ^ (wvar u₀ k₀ u s - 1) * Complex.exp (-(rate g * (ρ : ℂ)))))
      (Set.Ioi 0) :=
    (GammaRate.integrableOn_cpow_mul_exp_neg_mul (rate_re_pos hg) hw).const_mul (zconst u₀ k₀ a g)
  exact h.congr_fun (halfLine_eqOn g u a s) measurableSet_Ioi

private theorem halfLine_integrable {g : M₂} (hg : g.det ≠ 0) {u s : ℂ} (hw : 0 < (wvar u₀ k₀ u s).re) (a : ZMod 2) :
    MeasureTheory.Integrable (halfLine u₀ k₀ g u a s) :=
  (halfLine_integrableOn hg hw a).integrable_of_forall_notMem_eq_zero fun ρ hρ => by
    simp only [halfLine, if_neg (fun h : 0 < ρ => hρ (Set.mem_Ioi.mpr h))]

private theorem sgn_eq_one_or (g : M₂) : sgn g = 1 ∨ sgn g = -1 := by
  unfold sgn; split_ifs <;> simp

private theorem integral_halfLine {g : M₂} (hg : g.det ≠ 0) {u s : ℂ} (hw : 0 < (wvar u₀ k₀ u s).re) (a : ZMod 2) :
    ∫ ρ : ℝ, halfLine u₀ k₀ g u a s ρ =
      zconst u₀ k₀ a g *
        (Complex.Gamma (wvar u₀ k₀ u s) * Complex.exp (-(wvar u₀ k₀ u s * Complex.log (rate g)))) := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi 0)
    (fun ρ hρ => by simp only [halfLine, if_neg (fun h : 0 < ρ => hρ (Set.mem_Ioi.mpr h))])]
  rw [← MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (halfLine_eqOn g u a s)]

  have h1 : ∫ ρ : ℝ in Set.Ioi 0,
        zconst u₀ k₀ a g * ((ρ : ℂ) ^ (wvar u₀ k₀ u s - 1) * Complex.exp (-(rate g * (ρ : ℂ)))) =
      zconst u₀ k₀ a g * ∫ ρ : ℝ in Set.Ioi 0, (ρ : ℂ) ^ (wvar u₀ k₀ u s - 1) * Complex.exp (-(rate g * (ρ : ℂ))) :=
    MeasureTheory.integral_const_mul _ _
  rw [h1, GammaRate.integral_cpow_mul_exp_neg_mul_eq_exp_log (rate_re_pos hg) hw]

private theorem zeta_integrable {g : M₂} (hg : g.det ≠ 0) (u : ℂ) (a : ZMod 2) {s : ℂ}
    (hs : -(shift u₀ k₀).re < s.re + u.re) : MeasureTheory.Integrable (zetaIntegrand (W u₀ k₀) g u a s) := by
  rw [zetaIntegrand_eq_halfLine hg]
  have hw := wvar_re_pos hs
  rcases sgn_eq_one_or g with h | h
  · simpa only [h, one_mul] using halfLine_integrable hg hw a
  · simpa only [h, neg_one_mul] using (halfLine_integrable hg hw a).comp_neg

private theorem archFactor_twist_P (u : ℂ) (a : ZMod 2) (s : ℂ) :
    ((P u₀ k₀ hk).twist u a).archFactor s = Gammaℂ (wvar u₀ k₀ u s) := by
  simp only [P, RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC,
    Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton, Multiset.prod_singleton, one_mul, wvar, shift]
  congr 1; ring

private theorem zeta_eq {g : M₂} (hg : g.det ≠ 0) (u : ℂ) (a : ZMod 2) {s : ℂ} (hs : -(shift u₀ k₀).re < s.re + u.re) :
    ∫ τ : ℝ, zetaIntegrand (W u₀ k₀) g u a s τ = ((P u₀ k₀ hk).twist u a).archFactor s * zetaEnt u₀ k₀ g u a s := by
  have hw := wvar_re_pos hs
  have hint : ∫ τ : ℝ, zetaIntegrand (W u₀ k₀) g u a s τ = ∫ ρ : ℝ, halfLine u₀ k₀ g u a s ρ := by
    rw [zetaIntegrand_eq_halfLine hg]
    rcases sgn_eq_one_or g with h | h
    · simp only [h, one_mul]
    · simp only [h, neg_one_mul]
      exact MeasureTheory.integral_neg_eq_self (halfLine u₀ k₀ g u a s) MeasureTheory.volume
  rw [hint, integral_halfLine hg hw a, archFactor_twist_P]
  unfold zetaEnt
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  rw [Gammaℂ_def, Complex.cpow_def_of_ne_zero h2π]
  have hE : Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * -wvar u₀ k₀ u s) *
      Complex.exp (wvar u₀ k₀ u s * (Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g))) =
      Complex.exp (-(wvar u₀ k₀ u s * Complex.log (rate g))) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [mul_neg] at hE ⊢
  linear_combination (-(Complex.Gamma (wvar u₀ k₀ u s) * zconst u₀ k₀ a g)) * hE

private theorem zetaEnt_finiteOrder (g : M₂) (u : ℂ) (a : ZMod 2) (A B : ℝ) :
    ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
      ‖zetaEnt u₀ k₀ g u a s‖ ≤ C * Real.exp (D * |s.im|) := by
  set L : ℂ := Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g) with hL
  set R₀ : ℝ := |A| + |B| + ‖u‖ + ‖shift u₀ k₀‖ with hR₀
  refine ⟨‖(1 / 2 : ℂ) * zconst u₀ k₀ a g‖ * Real.exp (‖L‖ * R₀), ‖L‖, fun s hA hB => ?_⟩
  have hw_bound : ‖wvar u₀ k₀ u s‖ ≤ R₀ + |s.im| := by

    have h1 : ‖wvar u₀ k₀ u s‖ ≤ ‖s‖ + ‖u‖ + ‖shift u₀ k₀‖ := by
      unfold wvar; linarith [norm_add_le (s + u) (shift u₀ k₀), norm_add_le s u]
    have h2 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    have h3 : |s.re| ≤ |A| + |B| := by
      rcases le_total 0 s.re with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self B, abs_nonneg A]
      · rw [abs_of_nonpos h]; linarith [neg_le_abs A, abs_nonneg B]
    rw [hR₀]; linarith
  have hnorm : ‖zetaEnt u₀ k₀ g u a s‖
      = ‖(1 / 2 : ℂ) * zconst u₀ k₀ a g‖ * Real.exp ((wvar u₀ k₀ u s * L).re) := by
    unfold zetaEnt; rw [norm_mul, Complex.norm_exp]
  rw [hnorm, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  calc (wvar u₀ k₀ u s * L).re ≤ ‖wvar u₀ k₀ u s * L‖ := Complex.re_le_norm _
    _ = ‖L‖ * ‖wvar u₀ k₀ u s‖ := by rw [norm_mul, mul_comm]
    _ ≤ ‖L‖ * (R₀ + |s.im|) := mul_le_mul_of_nonneg_left hw_bound (norm_nonneg _)
    _ = ‖L‖ * R₀ + ‖L‖ * |s.im| := by ring

private theorem weyl_mul_apply (g : M₂) : weyl * g = !![g 1 0, g 1 1; -g 0 0, -g 0 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [weyl, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_weyl_mul (g : M₂) : (weyl * g).det = g.det := by
  rw [Matrix.det_mul]; simp [weyl, Matrix.det_fin_two_of]

private theorem sgn_weyl_mul (g : M₂) : sgn (weyl * g) = sgn g := by
  unfold sgn; rw [det_weyl_mul]

private theorem chiSign_weyl_mul (a : ZMod 2) (g : M₂) : chiSign a (weyl * g) = chiSign a g := by
  unfold chiSign; rw [sgn_weyl_mul]

private def qq (g : M₂) : ℝ := ix g ^ 2 + iy g ^ 2

private theorem iy_ne_zero {g : M₂} (hg : g.det ≠ 0) : iy g ≠ 0 := fun h => by
  have := sgn_mul_iy_pos hg; rw [h, mul_zero] at this; exact lt_irrefl _ this

private theorem qq_pos {g : M₂} (hg : g.det ≠ 0) : 0 < qq g := by
  have := iy_ne_zero hg
  unfold qq; positivity

private theorem top_row_eq {g : M₂} (hg : g.det ≠ 0) :
    g 0 0 = iy g * g 1 1 + ix g * g 1 0 ∧ g 0 1 = ix g * g 1 1 - iy g * g 1 0 := by
  have ht := nsq_pos_of_det_ne_zero hg
  have ht0 : nsq g ≠ 0 := ht.ne'
  unfold ix iy at *
  rw [Matrix.det_fin_two] at *
  unfold nsq at *
  constructor <;> field_simp <;> ring

private theorem nsq_weyl_mul {g : M₂} (hg : g.det ≠ 0) : nsq (weyl * g) = nsq g * qq g := by
  obtain ⟨ha, hb⟩ := top_row_eq hg
  rw [weyl_mul_apply]
  unfold nsq qq
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]

  have hnsq : nsq g = g 1 0 ^ 2 + g 1 1 ^ 2 := rfl
  rw [hnsq] at *

  conv_lhs => rw [ha, hb]
  ring

private theorem det_fin_two' (g : M₂) : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

private theorem iy_weyl_mul {g : M₂} (hg : g.det ≠ 0) : iy (weyl * g) = iy g / qq g := by
  have hq := (qq_pos hg).ne'
  have ht := (nsq_pos_of_det_ne_zero hg).ne'
  unfold iy
  rw [det_weyl_mul, nsq_weyl_mul hg]
  field_simp

private theorem ix_weyl_mul {g : M₂} (hg : g.det ≠ 0) : ix (weyl * g) = -ix g / qq g := by
  have hq := (qq_pos hg).ne'
  have ht := (nsq_pos_of_det_ne_zero hg).ne'
  obtain ⟨ha, hb⟩ := top_row_eq hg
  have hnum : (weyl * g) 0 0 * (weyl * g) 1 0 + (weyl * g) 0 1 * (weyl * g) 1 1 =
      -(g 0 0 * g 1 0 + g 0 1 * g 1 1) := by
    rw [weyl_mul_apply]; simp; ring
  unfold ix
  rw [hnum, nsq_weyl_mul hg]
  field_simp

private theorem kap_weyl_mul {g : M₂} (hg : g.det ≠ 0) :
    kap (weyl * g) = I * ((iy g : ℂ) + (ix g : ℂ) * I) / (Real.sqrt (qq g) : ℂ) * kap g := by
  obtain ⟨ha, hb⟩ := top_row_eq hg
  have ht := nsq_pos_of_det_ne_zero hg
  have hq := qq_pos hg
  have hsq : Real.sqrt (nsq (weyl * g)) = Real.sqrt (nsq g) * Real.sqrt (qq g) := by
    rw [nsq_weyl_mul hg, Real.sqrt_mul ht.le]
  have hst : (Real.sqrt (nsq g) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hsq0 : (Real.sqrt (qq g) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  unfold kap
  rw [hsq, weyl_mul_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [ha, hb]
  push_cast
  field_simp
  apply Complex.ext <;> simp <;> ring

private theorem kap_weyl_mul_pow {g : M₂} (hg : g.det ≠ 0) :
    kap (weyl * g) ^ (k₀ + 1)
      = (I * ((iy g : ℂ) + (ix g : ℂ) * I) / (Real.sqrt (qq g) : ℂ)) ^ (k₀ + 1) * kap g ^ (k₀ + 1) := by
  rw [kap_weyl_mul hg, mul_pow]

private theorem chiSign_add (a b : ZMod 2) (g : M₂) : chiSign (a + b) g = chiSign a g * chiSign b g := by
  have hs : (sgn g : ℂ) * (sgn g : ℂ) = 1 := by
    have := sgn_sq g; rw [sq] at this; exact_mod_cast this
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  unfold chiSign
  by_cases ha : a = 0
  · subst ha; rw [zero_add, if_pos rfl, one_mul]
  · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
    subst ha1
    rw [if_neg h10]
    by_cases hb : b = 0
    · subst hb; rw [add_zero, if_neg h10, if_pos rfl, mul_one]
    · have hb1 : b = 1 := Fin.eq_one_of_ne_zero b hb
      subst hb1
      rw [h11, if_pos rfl, if_neg h10, hs]

private theorem chiSign_natCast_add_one (g : M₂) : chiSign ((k₀ : ZMod 2) + 1) g = (sgn g : ℂ) ^ (k₀ + 1) := by
  have hs : (sgn g : ℂ) ^ 2 = 1 := by exact_mod_cast sgn_sq g
  unfold chiSign
  split_ifs with h
  · have he : Even (k₀ + 1) := by rw [← ZMod.natCast_eq_zero_iff_even]; exact_mod_cast h
    obtain ⟨r, hr⟩ := he
    rw [hr, ← two_mul, pow_mul, hs, one_pow]
  · have ho : Odd (k₀ + 1) := by
      rcases Nat.even_or_odd (k₀ + 1) with he | ho
      · exact absurd (by rw [← ZMod.natCast_eq_zero_iff_even] at he; exact_mod_cast he) h
      · exact ho
    obtain ⟨r, hr⟩ := ho
    rw [hr, pow_succ, pow_mul, hs, one_pow, one_mul]

private theorem detAbsPow_weyl_mul (g : M₂) : detAbsPow u₀ (weyl * g) = detAbsPow u₀ g := by
  simp only [detAbsPow, det_weyl_mul]

private theorem zconst_weyl_mul {g : M₂} (hg : g.det ≠ 0) (a : ZMod 2) :
    zconst u₀ k₀ (a + ((k₀ : ZMod 2) + 1)) (weyl * g)
      = I ^ (k₀ + 1) * ((iy g : ℂ) + (ix g : ℂ) * I) ^ (k₀ + 1) / (qq g : ℂ) ^ (k₀ + 1) * (sgn g : ℂ) ^ (k₀ + 1) *
          zconst u₀ k₀ a g := by
  have hq := qq_pos hg
  have ht := nsq_pos_of_det_ne_zero hg
  have hsqq : (Real.sqrt (qq g) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have habs : |iy (weyl * g)| = |iy g| / qq g := by rw [iy_weyl_mul hg, abs_div, abs_of_pos hq]
  have hrpow : (|iy g| / qq g) ^ pexp k₀ = |iy g| ^ pexp k₀ / Real.sqrt (qq g) ^ (k₀ + 2) := by
    rw [Real.div_rpow (abs_nonneg _) hq.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    unfold pexp; push_cast; ring
  have hsqrt : Real.sqrt (nsq (weyl * g)) = Real.sqrt (nsq g) * Real.sqrt (qq g) := by
    rw [nsq_weyl_mul hg, Real.sqrt_mul ht.le]
  have hqr : (qq g : ℂ) = (Real.sqrt (qq g) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]
  unfold zconst
  rw [chiSign_weyl_mul, chiSign_add, chiSign_natCast_add_one, habs, hrpow, kap_weyl_mul_pow hg, hsqrt,
    detAbsPow_weyl_mul, div_pow, mul_pow]
  push_cast
  rw [hqr]
  have hpow : (Real.sqrt (qq g) : ℂ) ^ (k₀ + 2) ≠ 0 := pow_ne_zero _ hsqq
  have hpow' : (Real.sqrt (qq g) : ℂ) ^ (k₀ + 1) ≠ 0 := pow_ne_zero _ hsqq
  have hpow2 : ((Real.sqrt (qq g) : ℂ) ^ 2) ^ (k₀ + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hsqq)
  field_simp
  ring

private theorem rate_weyl_mul {g : M₂} (hg : g.det ≠ 0) :
    rate (weyl * g) = (((2 * Real.pi) ^ 2 : ℝ) : ℂ) * (rate g)⁻¹ := by
  have hq := qq_pos hg
  have hq0 : (qq g : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr := (rate_ne_zero hg)
  rw [eq_mul_inv_iff_mul_eq₀ hr]
  unfold rate
  rw [sgn_weyl_mul, iy_weyl_mul hg, ix_weyl_mul hg]
  rcases sgn_eq_one_or g with h | h <;> simp only [h] <;> push_cast <;> field_simp <;>
    (apply Complex.ext <;> simp [qq, sq] <;> ring)

private theorem log_rate_weyl_mul {g : M₂} (hg : g.det ≠ 0) :
    Complex.log (rate (weyl * g)) = 2 * Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g) := by
  have hr := rate_re_pos hg
  have hr0 := rate_ne_zero hg
  have h2π : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have harg : (rate g).arg ≠ Real.pi := by
    intro h; rw [Complex.arg_eq_pi_iff] at h; linarith [h.1]
  rw [rate_weyl_mul hg, Complex.log_ofReal_mul h2π (inv_ne_zero hr0), Complex.log_inv _ harg, Real.log_pow,
    ← sub_eq_add_neg]
  congr 1
  push_cast
  rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  push_cast
  ring

private theorem lconst_weyl_mul {g : M₂} (hg : g.det ≠ 0) :
    Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate (weyl * g)) =
      -(Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g)) := by
  rw [log_rate_weyl_mul hg]; ring

private theorem exp_neg_lconst {g : M₂} (hg : g.det ≠ 0) :
    Complex.exp (-(Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g))) =
      (sgn g : ℂ) * ((iy g : ℂ) - (ix g : ℂ) * I) := by
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  rw [neg_sub, Complex.exp_sub, Complex.exp_log (rate_ne_zero hg), Complex.exp_log h2π]
  unfold rate; field_simp

private theorem exp_neg_pow_lconst {g : M₂} (hg : g.det ≠ 0) :
    Complex.exp (-(((k₀ : ℂ) + 1) * (Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g)))) =
      (sgn g : ℂ) ^ (k₀ + 1) * ((iy g : ℂ) - (ix g : ℂ) * I) ^ (k₀ + 1) := by
  rw [show -(((k₀ : ℂ) + 1) * (Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g)))
      = ((k₀ + 1 : ℕ) : ℂ) * (-(Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g))) by push_cast; ring,
    Complex.exp_nat_mul, exp_neg_lconst hg, mul_pow]

private theorem centralExponent_P : (P u₀ k₀ hk).centralExponent = 2 * u₀ := by
  simp [P, RealArchParam.centralExponent]

private theorem centralSign_P : (P u₀ k₀ hk).centralSign = (k₀ : ZMod 2) + 1 := by
  simp [P, RealArchParam.centralSign]

private theorem epsilonFactor_twist_P (u : ℂ) (a : ZMod 2) : ((P u₀ k₀ hk).twist u a).epsilonFactor = I ^ (k₀ + 1) := by
  simp [P, RealArchParam.twist, RealArchParam.epsilonFactor]

private theorem wvar_dual (u s : ℂ) : wvar u₀ k₀ (-(u + 2 * u₀)) (1 - s) = (k₀ : ℂ) + 1 - wvar u₀ k₀ u s := by
  unfold wvar shift; ring

private theorem functional_equation (g : M₂) (u : ℂ) (a : ZMod 2) (s : ℂ) (hg : g.det ≠ 0) :
    zetaEnt u₀ k₀ (weyl * g) (-(u + (P u₀ k₀ hk).centralExponent)) (a + (P u₀ k₀ hk).centralSign) (1 - s) =
      ((P u₀ k₀ hk).twist u a).epsilonFactor * zetaEnt u₀ k₀ g u a s := by
  rw [centralExponent_P, centralSign_P, epsilonFactor_twist_P]
  unfold zetaEnt
  rw [wvar_dual, zconst_weyl_mul hg a, lconst_weyl_mul hg]
  set L := Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g) with hL
  set w := wvar u₀ k₀ u s with hw
  set β := (iy g : ℂ) + (ix g : ℂ) * I with hβ
  set β' := (iy g : ℂ) - (ix g : ℂ) * I with hβ'
  have hq := qq_pos hg
  have hq0 : (qq g : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqC : β' * β = (qq g : ℂ) := by
    rw [hβ, hβ']; unfold qq; push_cast; linear_combination (-(ix g : ℂ) ^ 2) * I_sq
  have hexp : Complex.exp (((k₀ : ℂ) + 1 - w) * -L)
      = (sgn g : ℂ) ^ (k₀ + 1) * β' ^ (k₀ + 1) * Complex.exp (w * L) := by
    rw [← exp_neg_pow_lconst hg, ← Complex.exp_add]; congr 1; ring
  rw [hexp]
  have hs : (sgn g : ℂ) ^ (k₀ + 1) * (sgn g : ℂ) ^ (k₀ + 1) = 1 := by
    rw [← mul_pow, show (sgn g : ℂ) * (sgn g : ℂ) = 1 by
      have := sgn_sq g; rw [sq] at this; exact_mod_cast this, one_pow]
  have hbb : β ^ (k₀ + 1) * β' ^ (k₀ + 1) = (qq g : ℂ) ^ (k₀ + 1) := by
    rw [← mul_pow, mul_comm, hqC]
  have key : β ^ (k₀ + 1) * β' ^ (k₀ + 1) * ((sgn g : ℂ) ^ (k₀ + 1) * (sgn g : ℂ) ^ (k₀ + 1)) / (qq g : ℂ) ^ (k₀ + 1)
      = 1 := by
    rw [hbb, hs, mul_one, div_self (pow_ne_zero _ hq0)]
  calc (1 / 2 : ℂ) * (I ^ (k₀ + 1) * β ^ (k₀ + 1) / (qq g : ℂ) ^ (k₀ + 1) * (sgn g : ℂ) ^ (k₀ + 1) *
          zconst u₀ k₀ a g) * ((sgn g : ℂ) ^ (k₀ + 1) * β' ^ (k₀ + 1) * Complex.exp (w * L))
        = I ^ (k₀ + 1) * ((1 / 2 : ℂ) * zconst u₀ k₀ a g * Complex.exp (w * L)) *
            (β ^ (k₀ + 1) * β' ^ (k₀ + 1) * ((sgn g : ℂ) ^ (k₀ + 1) * (sgn g : ℂ) ^ (k₀ + 1)) /
              (qq g : ℂ) ^ (k₀ + 1)) := by ring
    _ = _ := by rw [key, mul_one]

local notation "X₄" => (Fin 2 → Fin 2 → ℝ)

private def tX (m : X₄) : ℝ := nsq (Matrix.of m)

private def dX (m : X₄) : ℝ := (Matrix.of m).det

private def nX (m : X₄) : ℝ := (Matrix.of m) 0 0 * (Matrix.of m) 1 0 + (Matrix.of m) 0 1 * (Matrix.of m) 1 1

private theorem tX_eq (m : X₄) : tX m = m 1 0 ^ 2 + m 1 1 ^ 2 := rfl
private theorem dX_eq (m : X₄) : dX m = m 0 0 * m 1 1 - m 0 1 * m 1 0 := Matrix.det_fin_two _
private theorem nX_eq (m : X₄) : nX m = m 0 0 * m 1 0 + m 0 1 * m 1 1 := rfl

private theorem dX_pos {m : X₄} (hm : m ∈ posSet) : 0 < dX m := hm
private theorem tX_pos {m : X₄} (hm : m ∈ posSet) : 0 < tX m := nsq_pos_of_det_ne_zero (dX_pos hm).ne'

private inductive Ex : Type
  | const : ℂ → Ex
  | entry : Fin 2 → Fin 2 → Ex
  | tinv : Ex
  | dinv : Ex
  | add : Ex → Ex → Ex
  | mul : Ex → Ex → Ex

namespace Ex

private def eval : Ex → X₄ → ℂ
  | const c, _ => c
  | entry i j, m => (m i j : ℂ)
  | tinv, m => (((tX m)⁻¹ : ℝ) : ℂ)
  | dinv, m => (((dX m)⁻¹ : ℝ) : ℂ)
  | add p q, m => eval p m + eval q m
  | mul p q, m => eval p m * eval q m

private def dt (e : X₄) : Ex :=
  add (mul (const (2 * e 1 0)) (entry 1 0)) (mul (const (2 * e 1 1)) (entry 1 1))

private def dd (e : X₄) : Ex :=
  add (add (mul (const (e 0 0)) (entry 1 1)) (mul (const (e 1 1)) (entry 0 0)))
    (add (mul (const (-e 0 1)) (entry 1 0)) (mul (const (-e 1 0)) (entry 0 1)))

private def dn (e : X₄) : Ex :=
  add (add (mul (const (e 0 0)) (entry 1 0)) (mul (const (e 1 0)) (entry 0 0)))
    (add (mul (const (e 0 1)) (entry 1 1)) (mul (const (e 1 1)) (entry 0 1)))

private def D (e : X₄) : Ex → Ex
  | const _ => const 0
  | entry i j => const (e i j)
  | tinv => mul (const (-1)) (mul tinv (mul tinv (dt e)))
  | dinv => mul (const (-1)) (mul dinv (mul dinv (dd e)))
  | add p q => add (D e p) (D e q)
  | mul p q => add (mul (D e p) q) (mul p (D e q))

private theorem eval_dt (e m : X₄) : (dt e).eval m = (2 * e 1 0 * m 1 0 + 2 * e 1 1 * m 1 1 : ℝ) := by
  simp [dt, eval]
private theorem eval_dd (e m : X₄) :
    (dd e).eval m = (e 0 0 * m 1 1 + e 1 1 * m 0 0 - e 0 1 * m 1 0 - e 1 0 * m 0 1 : ℝ) := by
  simp [dd, eval]; ring
private theorem eval_dn (e m : X₄) :
    (dn e).eval m = (e 0 0 * m 1 0 + e 1 0 * m 0 0 + e 0 1 * m 1 1 + e 1 1 * m 0 1 : ℝ) := by
  simp [dn, eval]; ring

end Ex

private def coordCLM (i j : Fin 2) : X₄ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i)

private theorem coordCLM_apply (i j : Fin 2) (e : X₄) : coordCLM i j e = e i j := by
  simp [coordCLM]

private theorem hasFDerivAt_coord (i j : Fin 2) (m : X₄) : HasFDerivAt (fun m : X₄ => m i j) (coordCLM i j) m :=
  (coordCLM i j).hasFDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun e => (coordCLM_apply i j e).symm)

private def IsDeriv (f : X₄ → ℝ) (v : X₄ → X₄ → ℝ) (m : X₄) : Prop :=
  ∃ L : X₄ →L[ℝ] ℝ, HasFDerivAt f L m ∧ ∀ e, L e = v m e

private theorem isDeriv_tX (m : X₄) : IsDeriv tX (fun m e => 2 * e 1 0 * m 1 0 + 2 * e 1 1 * m 1 1) m := by
  have h := ((hasFDerivAt_coord 1 0 m).pow 2).add ((hasFDerivAt_coord 1 1 m).pow 2)
  refine ⟨_, h, fun e => ?_⟩
  simp [coordCLM_apply]; ring

private theorem isDeriv_dX (m : X₄) :
    IsDeriv dX (fun m e => e 0 0 * m 1 1 + e 1 1 * m 0 0 - e 0 1 * m 1 0 - e 1 0 * m 0 1) m := by
  have h := ((hasFDerivAt_coord 0 0 m).mul (hasFDerivAt_coord 1 1 m)).sub
    ((hasFDerivAt_coord 0 1 m).mul (hasFDerivAt_coord 1 0 m))
  have hd : HasFDerivAt dX
      (m 0 0 • coordCLM 1 1 + m 1 1 • coordCLM 0 0 - (m 0 1 • coordCLM 1 0 + m 1 0 • coordCLM 0 1)) m := by
    rw [show dX = fun m : X₄ => m 0 0 * m 1 1 - m 0 1 * m 1 0 from funext dX_eq]; exact h
  refine ⟨_, hd, fun e => ?_⟩
  simp [coordCLM_apply]; ring

private theorem isDeriv_nX (m : X₄) :
    IsDeriv nX (fun m e => e 0 0 * m 1 0 + e 1 0 * m 0 0 + e 0 1 * m 1 1 + e 1 1 * m 0 1) m := by
  have h := ((hasFDerivAt_coord 0 0 m).mul (hasFDerivAt_coord 1 0 m)).add
    ((hasFDerivAt_coord 0 1 m).mul (hasFDerivAt_coord 1 1 m))
  refine ⟨_, h, fun e => ?_⟩
  simp [coordCLM_apply]; ring

private theorem IsDeriv.inv {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (h : IsDeriv f v m) (hf : f m ≠ 0) :
    IsDeriv (fun m => (f m)⁻¹) (fun m e => -((f m)⁻¹ * (f m)⁻¹ * v m e)) m := by
  obtain ⟨L, hL, hv⟩ := h
  refine ⟨_, (hasDerivAt_inv hf).comp_hasFDerivAt m hL, fun e => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, hv, smul_eq_mul]
  field_simp

private def IsDerivC (f : X₄ → ℂ) (v : X₄ → X₄ → ℂ) (m : X₄) : Prop :=
  ∃ L : X₄ →L[ℝ] ℂ, HasFDerivAt f L m ∧ ∀ e, L e = v m e

private theorem IsDeriv.ofReal {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (h : IsDeriv f v m) :
    IsDerivC (fun m => (f m : ℂ)) (fun m e => (v m e : ℂ)) m := by
  obtain ⟨L, hL, hv⟩ := h
  refine ⟨Complex.ofRealCLM.comp L, Complex.ofRealCLM.hasFDerivAt.comp m hL, fun e => ?_⟩
  simp [hv]

private theorem IsDerivC.add {f g : X₄ → ℂ} {v w : X₄ → X₄ → ℂ} {m : X₄} (hf : IsDerivC f v m) (hg : IsDerivC g w m) :
    IsDerivC (fun m => f m + g m) (fun m e => v m e + w m e) m := by
  obtain ⟨L, hL, hv⟩ := hf; obtain ⟨L', hL', hw⟩ := hg
  exact ⟨L + L', hL.add hL', fun e => by simp [hv, hw]⟩

private theorem IsDerivC.mul {f g : X₄ → ℂ} {v w : X₄ → X₄ → ℂ} {m : X₄} (hf : IsDerivC f v m) (hg : IsDerivC g w m) :
    IsDerivC (fun m => f m * g m) (fun m e => v m e * g m + f m * w m e) m := by
  obtain ⟨L, hL, hv⟩ := hf; obtain ⟨L', hL', hw⟩ := hg
  refine ⟨f m • L' + g m • L, hL.mul hL', fun e => ?_⟩
  simp [hv, hw]; ring

private theorem IsDerivC.const (c : ℂ) (m : X₄) : IsDerivC (fun _ => c) (fun _ _ => 0) m :=
  ⟨0, hasFDerivAt_const c m, fun _ => rfl⟩

private theorem IsDerivC.differentiableAt {f : X₄ → ℂ} {v : X₄ → X₄ → ℂ} {m : X₄} (h : IsDerivC f v m) :
    DifferentiableAt ℝ f m := h.choose_spec.1.differentiableAt

private theorem IsDerivC.fderiv_apply {f : X₄ → ℂ} {v : X₄ → X₄ → ℂ} {m : X₄} (h : IsDerivC f v m) (e : X₄) :
    fderiv ℝ f m e = v m e := by
  obtain ⟨L, hL, hv⟩ := h
  rw [hL.fderiv, hv]

private theorem Ex.isDerivC (p : Ex) {m : X₄} (hm : m ∈ posSet) :
    IsDerivC p.eval (fun m e => (Ex.D e p).eval m) m := by
  induction p with
  | const c => exact IsDerivC.const c m
  | entry i j =>
    have h : IsDeriv (fun m : X₄ => m i j) (fun _ e => e i j) m :=
      ⟨coordCLM i j, hasFDerivAt_coord i j m, fun e => coordCLM_apply i j e⟩
    exact h.ofReal
  | tinv =>
    have h := ((isDeriv_tX m).inv (tX_pos hm).ne').ofReal
    obtain ⟨L, hL, hv⟩ := h
    refine ⟨L, hL, fun e => ?_⟩
    rw [hv]; simp only [Ex.eval, Ex.D, Ex.eval_dt]; push_cast; ring
  | dinv =>
    have h := ((isDeriv_dX m).inv (dX_pos hm).ne').ofReal
    obtain ⟨L, hL, hv⟩ := h
    refine ⟨L, hL, fun e => ?_⟩
    rw [hv]; simp only [Ex.eval, Ex.D, Ex.eval_dd]; push_cast; ring
  | add p q hp hq =>
    obtain ⟨L, hL, hv⟩ := hp.add hq
    exact ⟨L, hL, fun e => by rw [hv]; simp only [Ex.eval, Ex.D]⟩
  | mul p q hp hq =>
    obtain ⟨L, hL, hv⟩ := hp.mul hq
    exact ⟨L, hL, fun e => by rw [hv]; simp only [Ex.eval, Ex.D]⟩

private def xq (m : X₄) : ℝ := nX m / tX m

private def yq (m : X₄) : ℝ := dX m / tX m

private theorem ix_of (m : X₄) : ix (Matrix.of m) = xq m := rfl
private theorem iy_of (m : X₄) : iy (Matrix.of m) = yq m := rfl

private def env (u₀ : ℂ) (k₀ : ℕ) (m : X₄) : ℂ :=
  ((dX m ^ pexp k₀ : ℝ) : ℂ) * Complex.exp (u₀ * (Real.log (dX m) : ℂ)) * psi (xq m) *
    ((Real.exp (-(2 * Real.pi * yq m)) : ℝ) : ℂ)

namespace Ex

private def nEx : Ex := add (mul (entry 0 0) (entry 1 0)) (mul (entry 0 1) (entry 1 1))

private def dEx : Ex := add (mul (entry 0 0) (entry 1 1)) (mul (const (-1)) (mul (entry 0 1) (entry 1 0)))

private def dxq (e : X₄) : Ex := add (mul (dn e) tinv) (mul (const (-1)) (mul nEx (mul tinv (mul tinv (dt e)))))

private def dyq (e : X₄) : Ex := add (mul (dd e) tinv) (mul (const (-1)) (mul dEx (mul tinv (mul tinv (dt e)))))

private def A (u₀ : ℂ) (k₀ : ℕ) (e : X₄) : Ex :=
  add (mul (const (((pexp k₀ : ℝ) : ℂ) + u₀)) (mul dinv (dd e)))
    (add (mul (const (2 * Real.pi * I)) (dxq e)) (mul (const (-(2 * Real.pi))) (dyq e)))

private theorem eval_nEx (m : X₄) : nEx.eval m = (nX m : ℂ) := by simp [nEx, eval, nX_eq]
private theorem eval_dEx (m : X₄) : dEx.eval m = (dX m : ℂ) := by simp [dEx, eval, dX_eq]; ring

end Ex

private theorem IsDeriv.mul {f g : X₄ → ℝ} {v w : X₄ → X₄ → ℝ} {m : X₄} (hf : IsDeriv f v m) (hg : IsDeriv g w m) :
    IsDeriv (fun m => f m * g m) (fun m e => v m e * g m + f m * w m e) m := by
  obtain ⟨L, hL, hv⟩ := hf; obtain ⟨L', hL', hw⟩ := hg
  refine ⟨f m • L' + g m • L, hL.mul hL', fun e => ?_⟩
  simp [hv, hw]; ring

private theorem IsDeriv.const_mul {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (c : ℝ) (hf : IsDeriv f v m) :
    IsDeriv (fun m => c * f m) (fun m e => c * v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨c • L, hL.const_mul c, fun e => by simp [hv]⟩

private theorem IsDeriv.neg {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (hf : IsDeriv f v m) :
    IsDeriv (fun m => -f m) (fun m e => -v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨-L, hL.neg, fun e => by simp [hv]⟩

private theorem IsDeriv.rexp {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (hf : IsDeriv f v m) :
    IsDeriv (fun m => Real.exp (f m)) (fun m e => Real.exp (f m) * v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨Real.exp (f m) • L, (Real.hasDerivAt_exp (f m)).comp_hasFDerivAt m hL, fun e => by simp [hv]⟩

private theorem IsDeriv.rpow {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (r : ℝ) (hf : IsDeriv f v m) (h0 : f m ≠ 0) :
    IsDeriv (fun m => f m ^ r) (fun m e => r * f m ^ (r - 1) * v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨(r * f m ^ (r - 1)) • L, (Real.hasDerivAt_rpow_const (Or.inl h0)).comp_hasFDerivAt m hL,
    fun e => by simp [hv]⟩

private theorem IsDeriv.log {f : X₄ → ℝ} {v : X₄ → X₄ → ℝ} {m : X₄} (hf : IsDeriv f v m) (h0 : f m ≠ 0) :
    IsDeriv (fun m => Real.log (f m)) (fun m e => (f m)⁻¹ * v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨(f m)⁻¹ • L, (Real.hasDerivAt_log h0).comp_hasFDerivAt m hL, fun e => by simp [hv]⟩

private theorem IsDerivC.const_mul {f : X₄ → ℂ} {v : X₄ → X₄ → ℂ} {m : X₄} (c : ℂ) (hf : IsDerivC f v m) :
    IsDerivC (fun m => c * f m) (fun m e => c * v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨c • L, hL.const_mul c, fun e => by simp [hv]⟩

private theorem IsDerivC.cexp {f : X₄ → ℂ} {v : X₄ → X₄ → ℂ} {m : X₄} (hf : IsDerivC f v m) :
    IsDerivC (fun m => Complex.exp (f m)) (fun m e => Complex.exp (f m) * v m e) m := by
  obtain ⟨L, hL, hv⟩ := hf
  exact ⟨Complex.exp (f m) • L, (Complex.hasDerivAt_exp (f m)).comp_hasFDerivAt m hL, fun e => by simp [hv]⟩

private theorem isDeriv_xq {m : X₄} (hm : m ∈ posSet) :
    IsDeriv xq (fun m e => (e 0 0 * m 1 0 + e 1 0 * m 0 0 + e 0 1 * m 1 1 + e 1 1 * m 0 1) * (tX m)⁻¹ +
      nX m * -((tX m)⁻¹ * (tX m)⁻¹ * (2 * e 1 0 * m 1 0 + 2 * e 1 1 * m 1 1))) m := by
  have h : xq = fun m => nX m * (tX m)⁻¹ := funext fun m => div_eq_mul_inv _ _
  rw [h]
  exact (isDeriv_nX m).mul ((isDeriv_tX m).inv (tX_pos hm).ne')

private theorem isDeriv_yq {m : X₄} (hm : m ∈ posSet) :
    IsDeriv yq (fun m e => (e 0 0 * m 1 1 + e 1 1 * m 0 0 - e 0 1 * m 1 0 - e 1 0 * m 0 1) * (tX m)⁻¹ +
      dX m * -((tX m)⁻¹ * (tX m)⁻¹ * (2 * e 1 0 * m 1 0 + 2 * e 1 1 * m 1 1))) m := by
  have h : yq = fun m => dX m * (tX m)⁻¹ := funext fun m => div_eq_mul_inv _ _
  rw [h]
  exact (isDeriv_dX m).mul ((isDeriv_tX m).inv (tX_pos hm).ne')

private theorem env_isDerivC {m : X₄} (hm : m ∈ posSet) :
    IsDerivC (env u₀ k₀) (fun m e => env u₀ k₀ m * (Ex.A u₀ k₀ e).eval m) m := by
  have hd0 := (dX_pos hm).ne'
  have h1 := ((isDeriv_dX m).rpow (pexp k₀) hd0).ofReal
  have h1' : IsDerivC (fun m => Complex.exp (u₀ * (Real.log (dX m) : ℂ))) _ m :=
    ((((isDeriv_dX m).log hd0).ofReal).const_mul u₀).cexp
  have h2 : IsDerivC (fun m => psi (xq m)) _ m :=
    ((((isDeriv_xq hm).ofReal).const_mul (2 * (Real.pi : ℂ) * I)).cexp)
  have h3 := (((isDeriv_yq hm).const_mul (2 * Real.pi)).neg.rexp).ofReal
  obtain ⟨L, hL, hv⟩ := ((h1.mul h1').mul h2).mul h3
  refine ⟨L, ?_, fun e => ?_⟩
  · exact hL
  · rw [hv]
    have ht0 : (tX m : ℂ) ≠ 0 := by exact_mod_cast (tX_pos hm).ne'
    have hdC : (dX m : ℂ) ≠ 0 := by exact_mod_cast hd0
    simp only [env, psi, Ex.A, Ex.dxq, Ex.dyq, Ex.eval, Ex.eval_dd, Ex.eval_dn, Ex.eval_dt, Ex.eval_nEx,
      Ex.eval_dEx]
    rw [Real.rpow_sub_one hd0]
    push_cast
    field_simp
    ring

private theorem contDiffOn_tX {n : WithTop ℕ∞} : ContDiffOn ℝ n tX posSet := contDiff_nsqCoord.contDiffOn
private theorem contDiffOn_dX {n : WithTop ℕ∞} : ContDiffOn ℝ n dX posSet := contDiff_detCoord.contDiffOn
private theorem contDiffOn_nX {n : WithTop ℕ∞} : ContDiffOn ℝ n nX posSet := by
  have h : nX = fun m : X₄ => m 0 0 * m 1 0 + m 0 1 * m 1 1 := funext nX_eq
  rw [h]
  exact (((contDiff_coord 0 0).mul (contDiff_coord 1 0)).add
    ((contDiff_coord 0 1).mul (contDiff_coord 1 1))).contDiffOn

private theorem contDiffOn_ofReal {n : WithTop ℕ∞} {f : X₄ → ℝ} (hf : ContDiffOn ℝ n f posSet) :
    ContDiffOn ℝ n (fun m => (f m : ℂ)) posSet :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

private theorem Ex.contDiffOn (p : Ex) {n : WithTop ℕ∞} : ContDiffOn ℝ n p.eval posSet := by
  induction p with
  | const c => exact contDiffOn_const
  | entry i j => exact contDiffOn_ofReal (contDiff_coord i j).contDiffOn
  | tinv => exact contDiffOn_ofReal (contDiffOn_tX.inv fun m hm => (tX_pos hm).ne')
  | dinv => exact contDiffOn_ofReal (contDiffOn_dX.inv fun m hm => (dX_pos hm).ne')
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

private theorem contDiffOn_env {n : WithTop ℕ∞} : ContDiffOn ℝ n (env u₀ k₀) posSet := by
  have h1 : ContDiffOn ℝ n (fun m => ((dX m ^ pexp k₀ : ℝ) : ℂ)) posSet :=
    contDiffOn_ofReal (contDiffOn_dX.rpow_const_of_ne fun m hm => (dX_pos hm).ne')
  have h1' : ContDiffOn ℝ n (fun m => Complex.exp (u₀ * (Real.log (dX m) : ℂ))) posSet :=
    Complex.contDiff_exp.comp_contDiffOn
      (contDiffOn_const.mul (contDiffOn_ofReal (contDiffOn_dX.log fun m hm => (dX_pos hm).ne')))
  have hxq : ContDiffOn ℝ n xq posSet := contDiffOn_nX.div contDiffOn_tX fun m hm => (tX_pos hm).ne'
  have hyq : ContDiffOn ℝ n yq posSet := contDiffOn_dX.div contDiffOn_tX fun m hm => (tX_pos hm).ne'
  have h2 : ContDiffOn ℝ n (fun m => psi (xq m)) posSet :=
    Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul (contDiffOn_ofReal hxq))
  have h3 : ContDiffOn ℝ n (fun m => ((Real.exp (-(2 * Real.pi * yq m)) : ℝ) : ℂ)) posSet :=
    contDiffOn_ofReal (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hyq).neg)
  exact ((h1.mul h1').mul h2).mul h3

namespace Ex

private def kEx : Ex := add (entry 1 1) (mul (const (-I)) (entry 1 0))

private def npow (p : Ex) : ℕ → Ex
  | 0 => const 1
  | n + 1 => mul (npow p n) p

private theorem eval_npow (p : Ex) (n : ℕ) (m : X₄) : (npow p n).eval m = p.eval m ^ n := by
  induction n with
  | zero => simp [npow, eval]
  | succ n ih => simp only [npow, eval, ih, pow_succ]

private def p₀ (k₀ : ℕ) : Ex := mul (npow kEx (k₀ + 1)) (npow tinv (k₀ + 1))
end Ex

private theorem asPi_W_eq_env_mul {m : X₄} (hm : m ∈ posSet) :
    asPi (W u₀ k₀) m = env u₀ k₀ m * (Ex.p₀ k₀).eval m := by
  have hd := dX_pos hm
  have ht := tX_pos hm
  have hsqrt_pos : 0 < Real.sqrt (tX m) := Real.sqrt_pos.mpr ht
  have hrpow : (dX m / tX m) ^ pexp k₀ = dX m ^ pexp k₀ / Real.sqrt (tX m) ^ (k₀ + 2) := by
    rw [Real.div_rpow hd.le ht.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    unfold pexp; push_cast; ring
  have hs0 : (Real.sqrt (tX m) : ℂ) ≠ 0 := by exact_mod_cast hsqrt_pos.ne'
  have htr : (tX m : ℂ) = (Real.sqrt (tX m) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  simp only [asPi, W, if_pos (show 0 < (Matrix.of m).det from hm), ix_of, iy_of, prof, env, detPow, Ex.p₀,
    Ex.eval, Ex.eval_npow, Ex.kEx, kap, Matrix.of_apply]
  rw [show yq m = dX m / tX m from rfl, hrpow, show nsq (Matrix.of m) = tX m from rfl,
    show (Matrix.of m).det = dX m from rfl, div_pow]
  push_cast
  rw [htr]
  simp only [inv_pow]
  have hp1 : (Real.sqrt (tX m) : ℂ) ^ (k₀ + 1) ≠ 0 := pow_ne_zero _ hs0
  have hp2 : (Real.sqrt (tX m) : ℂ) ^ (k₀ + 2) ≠ 0 := pow_ne_zero _ hs0
  have hp3 : ((Real.sqrt (tX m) : ℂ) ^ 2) ^ (k₀ + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hs0)
  field_simp
  ring

private theorem diagOneMulCoords_apply₀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    diagOneMulCoords y k 0 j = y * k 0 j := by
  simp [diagOneMulCoords, diagOne, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem diagOneMulCoords_apply₁ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    diagOneMulCoords y k 1 j = k 1 j := by
  simp [diagOneMulCoords, diagOne, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem IsK.rows {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    k 0 0 ^ 2 + k 0 1 ^ 2 = 1 ∧ k 0 0 * k 1 0 + k 0 1 * k 1 1 = 0 ∧ k 1 0 ^ 2 + k 1 1 ^ 2 = 1 := by
  have h : k * star k = 1 := (show star k * k = 1 ∧ k * star k = 1 from hk).2
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] at h00 h01 h11
  refine ⟨by nlinarith [h00], by nlinarith [h01], by nlinarith [h11]⟩

private theorem IsK.entry_abs_le {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) (i j : Fin 2) : |k i j| ≤ 1 := by
  obtain ⟨h0, -, h1⟩ := IsK.rows hk
  have hsq : k i j ^ 2 ≤ 1 := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      nlinarith [sq_nonneg (k 0 0), sq_nonneg (k 0 1), sq_nonneg (k 1 0), sq_nonneg (k 1 1)]
  exact (sq_le_one_iff_abs_le_one _).mp hsq

private theorem tX_pt (y : ℝ) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : tX (diagOneMulCoords y k) = 1 := by
  rw [tX_eq, diagOneMulCoords_apply₁, diagOneMulCoords_apply₁]; exact (IsK.rows hk).2.2

private theorem nX_pt (y : ℝ) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : nX (diagOneMulCoords y k) = 0 := by
  rw [nX_eq, diagOneMulCoords_apply₀, diagOneMulCoords_apply₀, diagOneMulCoords_apply₁, diagOneMulCoords_apply₁]
  have := (IsK.rows hk).2.1
  linear_combination y * this

private theorem abs_dX_pt (y : ℝ) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : |dX (diagOneMulCoords y k)| = |y| := by
  obtain ⟨h0, h1, h2⟩ := IsK.rows hk
  rw [dX_eq, diagOneMulCoords_apply₀, diagOneMulCoords_apply₀, diagOneMulCoords_apply₁, diagOneMulCoords_apply₁]
  have hδ : (k 0 0 * k 1 1 - k 0 1 * k 1 0) ^ 2 = 1 := by
    linear_combination (k 1 0 ^ 2 + k 1 1 ^ 2) * h0 + h2 - (k 0 0 * k 1 0 + k 0 1 * k 1 1) * h1
  have habs : |k 0 0 * k 1 1 - k 0 1 * k 1 0| = 1 := by
    have h := sq_abs (k 0 0 * k 1 1 - k 0 1 * k 1 0)
    nlinarith [abs_nonneg (k 0 0 * k 1 1 - k 0 1 * k 1 0)]
  rw [show y * k 0 0 * k 1 1 - y * k 0 1 * k 1 0 = y * (k 0 0 * k 1 1 - k 0 1 * k 1 0) by ring, abs_mul, habs,
    mul_one]

private theorem pt_mem_glSet {y : ℝ} (hy : y ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    diagOneMulCoords y k ∈ glSet := by
  show dX (diagOneMulCoords y k) ≠ 0
  intro h
  have := abs_dX_pt y hk
  rw [h, abs_zero] at this
  exact hy (abs_eq_zero.mp this.symm)

private theorem dX_pt_of_mem_posSet {y : ℝ} {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k)
    (hpos : diagOneMulCoords y k ∈ posSet) : dX (diagOneMulCoords y k) = |y| := by
  rw [← abs_dX_pt y hk, abs_of_pos (dX_pos hpos)]

private theorem norm_env_pt {y : ℝ} {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) (hpos : diagOneMulCoords y k ∈ posSet) :
    ‖env u₀ k₀ (diagOneMulCoords y k)‖ = |y| ^ (pexp k₀ + u₀.re) * Real.exp (-(2 * Real.pi * |y|)) := by
  have hd := dX_pt_of_mem_posSet hk hpos
  have hy0 : 0 < |y| := hd ▸ dX_pos hpos
  have ht := tX_pt y hk
  have hn := nX_pt y hk
  simp only [env, xq, yq, hd, ht, hn, div_one, psi, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _),
    Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  rw [Real.rpow_add hy0, Real.rpow_def_of_pos hy0 u₀.re, mul_comm (Real.log |y|)]

private theorem Ex.bound (p : Ex) : ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), y ≠ 0 → IsK k →
    ‖p.eval (diagOneMulCoords y k)‖ ≤ C * (|y| + |y|⁻¹ + 1) ^ n := by
  induction p with
  | const c => exact ⟨‖c‖, norm_nonneg c, 0, fun y k _ _ => by simp [Ex.eval]⟩
  | entry i j =>
    refine ⟨1, zero_le_one, 1, fun y k hy hk => ?_⟩
    have hB := DecayScale.one_le_base y
    have hkij : |k i j| ≤ 1 := IsK.entry_abs_le hk i j
    simp only [Ex.eval, Complex.norm_real, Real.norm_eq_abs, one_mul, pow_one]
    fin_cases i
    · simp only [Fin.zero_eta, diagOneMulCoords_apply₀, abs_mul]
      have h0 : |k 0 j| ≤ 1 := by simpa using hkij
      nlinarith [abs_nonneg y, abs_nonneg (k 0 j), inv_nonneg.mpr (abs_nonneg y)]
    · simp only [Fin.mk_one, diagOneMulCoords_apply₁]
      have h1 : |k 1 j| ≤ 1 := by simpa using hkij
      linarith
  | tinv =>
    exact ⟨1, zero_le_one, 0, fun y k _ hk => by simp [Ex.eval, tX_pt y hk]⟩
  | dinv =>
    refine ⟨1, zero_le_one, 1, fun y k hy hk => ?_⟩
    simp only [Ex.eval, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_dX_pt y hk, one_mul, pow_one]
    linarith [abs_nonneg y]
  | add p q hp hq =>
    obtain ⟨C₁, hC₁, n₁, h₁⟩ := hp
    obtain ⟨C₂, hC₂, n₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, by positivity, max n₁ n₂, fun y k hy hk => ?_⟩
    have hB := DecayScale.one_le_base y
    have e₁ : (|y| + |y|⁻¹ + 1) ^ n₁ ≤ (|y| + |y|⁻¹ + 1) ^ max n₁ n₂ := pow_le_pow_right₀ hB (le_max_left _ _)
    have e₂ : (|y| + |y|⁻¹ + 1) ^ n₂ ≤ (|y| + |y|⁻¹ + 1) ^ max n₁ n₂ := pow_le_pow_right₀ hB (le_max_right _ _)
    calc ‖(Ex.add p q).eval (diagOneMulCoords y k)‖
        ≤ ‖p.eval (diagOneMulCoords y k)‖ + ‖q.eval (diagOneMulCoords y k)‖ := norm_add_le _ _
      _ ≤ C₁ * (|y| + |y|⁻¹ + 1) ^ n₁ + C₂ * (|y| + |y|⁻¹ + 1) ^ n₂ := add_le_add (h₁ y k hy hk) (h₂ y k hy hk)
      _ ≤ C₁ * (|y| + |y|⁻¹ + 1) ^ max n₁ n₂ + C₂ * (|y| + |y|⁻¹ + 1) ^ max n₁ n₂ :=
          add_le_add (mul_le_mul_of_nonneg_left e₁ hC₁) (mul_le_mul_of_nonneg_left e₂ hC₂)
      _ = (C₁ + C₂) * (|y| + |y|⁻¹ + 1) ^ max n₁ n₂ := by ring
  | mul p q hp hq =>
    obtain ⟨C₁, hC₁, n₁, h₁⟩ := hp
    obtain ⟨C₂, hC₂, n₂, h₂⟩ := hq
    refine ⟨C₁ * C₂, by positivity, n₁ + n₂, fun y k hy hk => ?_⟩
    have hB0 : (0 : ℝ) ≤ |y| + |y|⁻¹ + 1 := by positivity
    calc ‖(Ex.mul p q).eval (diagOneMulCoords y k)‖
        = ‖p.eval (diagOneMulCoords y k)‖ * ‖q.eval (diagOneMulCoords y k)‖ := norm_mul _ _
      _ ≤ (C₁ * (|y| + |y|⁻¹ + 1) ^ n₁) * (C₂ * (|y| + |y|⁻¹ + 1) ^ n₂) :=
          mul_le_mul (h₁ y k hy hk) (h₂ y k hy hk) (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * (|y| + |y|⁻¹ + 1) ^ (n₁ + n₂) := by rw [pow_add]; ring

private def Idx : Type := {q : ℝ × Matrix (Fin 2) (Fin 2) ℝ // q.1 ≠ 0 ∧ IsK q.2 ∧ diagOneMulCoords q.1 q.2 ∈ posSet}

private def ptI (i : Idx) : X₄ := diagOneMulCoords i.1.1 i.1.2

private def φ (n : ℕ) (i : Idx) : ℝ :=
  (|i.1.1| + |i.1.1|⁻¹ + 1) ^ n * |i.1.1| ^ (3 / 2 : ℝ) * Real.exp (-(2 * Real.pi * |i.1.1|))

private def InClass (u₀ : ℂ) (k₀ : ℕ) (f : X₄ → ℂ) : Prop :=
  ∃ p : Ex, Set.EqOn f (fun m => env u₀ k₀ m * p.eval m) posSet

private theorem InClass.contDiffOn {f : X₄ → ℂ} (hf : InClass u₀ k₀ f) : ContDiffOn ℝ (⊤ : ℕ∞) f posSet := by
  obtain ⟨p, hp⟩ := hf
  exact ((contDiffOn_env (u₀ := u₀) (k₀ := k₀)).mul p.contDiffOn).congr hp

private theorem exists_rpow_le_scale (r : ℝ) :
    ∃ M : ℕ, ∀ y : ℝ, y ≠ 0 → |y| ^ r ≤ (|y| + |y|⁻¹ + 1) ^ M * |y| ^ (3 / 2 : ℝ) := by
  refine ⟨⌈|r - 3 / 2|⌉₊, fun y hy => ?_⟩
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hbase1 : (1 : ℝ) ≤ |y| + |y|⁻¹ + 1 := DecayScale.one_le_base y
  have hM : |r - 3 / 2| ≤ (⌈|r - 3 / 2|⌉₊ : ℝ) := Nat.le_ceil _

  have hb : ∃ b : ℝ, 0 ≤ b ∧ b ≤ |y| + |y|⁻¹ + 1 ∧ |y| ^ (r - 3 / 2) = b ^ |r - 3 / 2| := by
    rcases le_or_gt 0 (r - 3 / 2) with h | h
    · exact ⟨|y|, hy0.le, by linarith [inv_pos.mpr hy0], by rw [abs_of_nonneg h]⟩
    · refine ⟨|y|⁻¹, (inv_pos.mpr hy0).le, by linarith, ?_⟩
      rw [abs_of_neg h, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le, neg_neg]
  obtain ⟨b, hb0, hbb, hbeq⟩ := hb
  have hsplit : |y| ^ r = |y| ^ (r - 3 / 2) * |y| ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hy0]; ring_nf
  rw [hsplit, hbeq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy0.le _)
  calc b ^ |r - 3 / 2| ≤ (|y| + |y|⁻¹ + 1) ^ |r - 3 / 2| :=
        Real.rpow_le_rpow hb0 hbb (abs_nonneg _)
    _ ≤ (|y| + |y|⁻¹ + 1) ^ ((⌈|r - 3 / 2|⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase1 hM
    _ = (|y| + |y|⁻¹ + 1) ^ ⌈|r - 3 / 2|⌉₊ := Real.rpow_natCast _ _

private theorem InClass.fderiv_apply {f : X₄ → ℂ} (hf : InClass u₀ k₀ f) (e : X₄) :
    InClass u₀ k₀ fun x => fderiv ℝ f x e := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨Ex.add (Ex.mul (Ex.A u₀ k₀ e) p) (Ex.D e p), fun x hx => ?_⟩
  have hEq : f =ᶠ[nhds x] fun m => env u₀ k₀ m * p.eval m :=
    Filter.eventuallyEq_of_mem (isOpen_posSet.mem_nhds hx) hp
  show fderiv ℝ f x e = _
  rw [hEq.fderiv_eq, ((env_isDerivC hx).mul (p.isDerivC hx)).fderiv_apply]
  simp only [Ex.eval]
  ring

private theorem InClass.bound {f : X₄ → ℂ} (hf : InClass u₀ k₀ f) : ∃ (C : ℝ) (n : ℕ), ∀ i : Idx, ‖f (ptI i)‖ ≤ C * φ n i := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨C, hC0, n, hCn⟩ := p.bound
  obtain ⟨M, hM⟩ := exists_rpow_le_scale (pexp k₀ + u₀.re)
  refine ⟨C, n + M, fun i => ?_⟩
  obtain ⟨⟨y, k⟩, hy, hk, hpos⟩ := i
  simp only [ptI] at hpos ⊢
  rw [hp hpos, norm_mul, norm_env_pt hk hpos]
  have h := hCn y k hy hk
  have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi * |y|)) := (Real.exp_pos _).le
  have hbase0 : 0 ≤ (|y| + |y|⁻¹ + 1) ^ M * |y| ^ (3 / 2 : ℝ) := by positivity
  calc |y| ^ (pexp k₀ + u₀.re) * Real.exp (-(2 * Real.pi * |y|)) * ‖p.eval (diagOneMulCoords y k)‖
      ≤ ((|y| + |y|⁻¹ + 1) ^ M * |y| ^ (3 / 2 : ℝ)) * Real.exp (-(2 * Real.pi * |y|)) *
          (C * (|y| + |y|⁻¹ + 1) ^ n) := by
        gcongr
        exact hM y hy
    _ = C * φ (n + M) ⟨⟨y, k⟩, hy, hk, hpos⟩ := by simp only [φ, pow_add]; ring

private theorem inClass_asPi_W : InClass u₀ k₀ (asPi (W u₀ k₀)) := ⟨Ex.p₀ k₀, fun _ hm => asPi_W_eq_env_mul hm⟩

private theorem iteratedFDerivWithin_asPi_W_bound (j : ℕ) :
    ∃ (C : ℝ) (n : ℕ), ∀ i : Idx, ‖iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) posSet (ptI i)‖ ≤ C * φ n i :=
  DerivBounds.iteratedFDerivWithin_bound_of_closed (Module.finBasis ℝ X₄) posSet isOpen_posSet ptI
    (fun i => i.2.2.2) φ (fun n i => DecayScale.scale_nonneg n i.1.1)
    (DecayScale.scale_monotone_family fun i : Idx => i.1.1) (InClass u₀ k₀) (fun _ hf => hf.contDiffOn)
    (fun _ hf _ => hf.fderiv_apply _) (fun _ hf => hf.bound) j (asPi (W u₀ k₀)) inClass_asPi_W

private theorem isOpen_glSet : IsOpen glSet := by rw [glSet_eq]; exact isOpen_posSet.union isOpen_negSet

private theorem iteratedFDerivWithin_glSet_of_pos (j : ℕ) {q : X₄} (hq : q ∈ posSet) :
    iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) glSet q
      = iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) posSet q := by
  have hgl : q ∈ glSet := by rw [glSet_eq]; exact Or.inl hq
  rw [iteratedFDerivWithin_of_isOpen j isOpen_glSet hgl, iteratedFDerivWithin_of_isOpen j isOpen_posSet hq]

private theorem iteratedFDerivWithin_glSet_of_neg (j : ℕ) {q : X₄} (hq : q ∈ negSet) :
    iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) glSet q = 0 := by
  have hgl : q ∈ glSet := by rw [glSet_eq]; exact Or.inr hq
  have hzero : Set.EqOn (asPi (W u₀ k₀)) (fun _ => (0 : ℂ)) negSet := fun m hm => by
    simp only [asPi, W, if_neg (not_lt.mpr (le_of_lt (show (Matrix.of m).det < 0 from hm)))]
  rw [iteratedFDerivWithin_of_isOpen j isOpen_glSet hgl, ← iteratedFDerivWithin_of_isOpen j isOpen_negSet hq,
    iteratedFDerivWithin_congr hzero hq, iteratedFDerivWithin_fun_zero]
  rfl

private theorem pos_or_neg {y : ℝ} (hy : y ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    diagOneMulCoords y k ∈ posSet ∨ diagOneMulCoords y k ∈ negSet := by
  have h := pt_mem_glSet hy hk
  rw [glSet_eq] at h
  exact h

private theorem decay_top (j N : ℕ) : ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → 1 ≤ |y| →
    ‖iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, n, hC⟩ := iteratedFDerivWithin_asPi_W_bound (u₀ := u₀) (k₀ := k₀) j
  obtain ⟨C', hC'⟩ := DecayScale.exists_scale_le_of_one_le_abs n N
  refine ⟨max C 0 * max C' 0, fun y k hk hy1 => ?_⟩
  have hy : y ≠ 0 := fun h => by rw [h, abs_zero] at hy1; linarith
  have hr0 : 0 ≤ |y| ^ (-(N : ℝ)) := Real.rpow_nonneg (abs_nonneg y) _
  rcases pos_or_neg hy hk with hpos | hneg
  · rw [iteratedFDerivWithin_glSet_of_pos j hpos]
    have h1 := hC ⟨⟨y, k⟩, hy, hk, hpos⟩
    have hφ0 : 0 ≤ φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ := DecayScale.scale_nonneg n y
    have h2 : φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ ≤ C' * |y| ^ (-(N : ℝ)) := hC' y hy1
    calc ‖iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) posSet (diagOneMulCoords y k)‖
        ≤ C * φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ := h1
      _ ≤ max C 0 * φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ := mul_le_mul_of_nonneg_right (le_max_left _ _) hφ0
      _ ≤ max C 0 * (C' * |y| ^ (-(N : ℝ))) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ ≤ max C 0 * (max C' 0 * |y| ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0) (le_max_right _ _)
      _ = max C 0 * max C' 0 * |y| ^ (-(N : ℝ)) := by ring
  · rw [iteratedFDerivWithin_glSet_of_neg j hneg, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) hr0

private theorem decay_zero (j : ℕ) : ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → y ≠ 0 → |y| ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ) := by
  obtain ⟨C, n, hC⟩ := iteratedFDerivWithin_asPi_W_bound (u₀ := u₀) (k₀ := k₀) j
  refine ⟨max C 0 * (3 : ℝ) ^ n, (n : ℝ), fun y k hk hy hy1 => ?_⟩
  have hr0 : 0 ≤ |y| ^ (-(n : ℝ)) := Real.rpow_nonneg (abs_nonneg y) _
  rcases pos_or_neg hy hk with hpos | hneg
  · rw [iteratedFDerivWithin_glSet_of_pos j hpos]
    have h1 := hC ⟨⟨y, k⟩, hy, hk, hpos⟩
    have hφ0 : 0 ≤ φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ := DecayScale.scale_nonneg n y
    have h2 : φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ ≤ (3 : ℝ) ^ n * |y| ^ (-(n : ℝ)) := DecayScale.scale_le_of_abs_le_one n hy hy1
    calc ‖iteratedFDerivWithin ℝ j (asPi (W u₀ k₀)) posSet (diagOneMulCoords y k)‖
        ≤ C * φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ := h1
      _ ≤ max C 0 * φ n ⟨⟨y, k⟩, hy, hk, hpos⟩ := mul_le_mul_of_nonneg_right (le_max_left _ _) hφ0
      _ ≤ max C 0 * ((3 : ℝ) ^ n * |y| ^ (-(n : ℝ))) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = max C 0 * (3 : ℝ) ^ n * |y| ^ (-(n : ℝ)) := by ring
  · rw [iteratedFDerivWithin_glSet_of_neg j hneg, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) hr0

end

end DiscreteFamily

open DiscreteFamily in

private def archDatumR_discreteMember (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) : ArchDatumR (P u₀ k₀ hk) where
  W := W u₀ k₀
  smooth := contDiffOn_asPi_W
  unip_law := fun x g => W_unip_mul x g
  central_law := fun _ g hz => W_smul hz g
  zetaEntire := zetaEnt u₀ k₀
  zetaEntire_differentiable := zetaEnt_differentiable
  zeta_abscissa := -(shift u₀ k₀).re
  zeta_integrable := fun _ u a _ hg hs => zeta_integrable hg u a hs
  zeta_eq := fun _ u a _ hg hs => zeta_eq hg u a hs
  functional_equation := functional_equation
  zetaEntire_finiteOrder := zetaEnt_finiteOrder
  decay_top := decay_top
  decay_zero := decay_zero

open DiscreteFamily in

private theorem archDatumR_discreteMember_W_one_ne_zero (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) :
    (archDatumR_discreteMember u₀ k₀ hk).W 1 ≠ 0 := by
  show W u₀ k₀ 1 ≠ 0
  have h1 : nsq (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [nsq]
  have hiy : iy (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [iy, h1]
  have hix : ix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by simp [ix, h1]
  have hkap : kap (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [kap, h1]
  unfold W
  rw [if_pos (by simp), hix, hiy, hkap, h1]
  simp [ArchR.psi, prof, detPow]

private theorem exists_archDatumR_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) :
    ∃ D : ArchDatumR (RealArchParam.discrete u₀ k₀ hk), ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 :=
  ⟨archDatumR_discreteMember u₀ k₀ hk, 1, by
    simpa using archDatumR_discreteMember_W_one_ne_zero u₀ k₀ hk⟩

namespace DiscreteFamily

p2m_open "LanglandsTunnell.Converse.ArchR"

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

section WeightOne

variable {u₀ : ℂ}

private def weightOneParam (u₀ : ℂ) : RealArchParam := RealArchParam.principal u₀ 0 u₀ 1

private theorem weightOneParam_zero : weightOneParam 0 = RealArchParam.oddArtin := rfl

private theorem centralExponent_weightOneParam : (weightOneParam u₀).centralExponent = 2 * u₀ := by
  simp [weightOneParam, RealArchParam.centralExponent, two_mul]

private theorem centralSign_weightOneParam : (weightOneParam u₀).centralSign = ((0 : ℕ) : ZMod 2) + 1 := by
  simp [weightOneParam, RealArchParam.centralSign]

private theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem epsilonFactor_twist_weightOneParam (u : ℂ) (a : ZMod 2) :
    ((weightOneParam u₀).twist u a).epsilonFactor = I ^ (0 + 1) := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    simp [weightOneParam, RealArchParam.twist, RealArchParam.epsilonFactor, signEpsilon,
      zmod_two_one_ne_zero, zmod_two_one_add_one]

private theorem archFactor_twist_weightOneParam (u : ℂ) (a : ZMod 2) (s : ℂ) :
    ((weightOneParam u₀).twist u a).archFactor s = Gammaℂ (wvar u₀ 0 u s) := by
  have hw : wvar u₀ 0 u s = s + u + u₀ := by unfold wvar shift; push_cast; ring
  rw [hw]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    simp [weightOneParam, RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR,
      RealArchParam.gammaC, signShift, zmod_two_one_ne_zero, zmod_two_one_add_one] <;>
    rw [← Gammaℝ_mul_Gammaℝ_add_one] <;> ring_nf

private theorem W_smul_weightOne {z : ℝ} (hz : z ≠ 0) (g : M₂) :
    W u₀ 0 (z • g) = centralChar (weightOneParam u₀) z * ((|z| : ℝ) : ℂ) * W u₀ 0 g := by
  unfold W
  have hpos : (0 < (z • g).det ↔ 0 < g.det) := by
    rw [det_smul']
    exact mul_pos_iff_of_pos_left (by positivity)
  by_cases h : 0 < g.det
  · rw [if_pos (hpos.mpr h), if_pos h, ix_smul hz, iy_smul hz, kap_smul hz, mul_pow, sqrt_nsq_smul,
      detPow_smul hz h]
    simp only [centralChar, centralExponent_weightOneParam, centralSign_weightOneParam, quasiChar,
      abs_cpow_eq hz]
    split_ifs with hpar
    · rw [sign_pow_of_even hz hpar]; push_cast; ring
    · rw [sign_pow_of_odd hz hpar]; push_cast; ring
  · rw [if_neg (fun h' => h (hpos.mp h')), if_neg h, mul_zero]

private theorem zeta_eq_weightOne {g : M₂} (hg : g.det ≠ 0) (u : ℂ) (a : ZMod 2) {s : ℂ}
    (hs : -(shift u₀ 0).re < s.re + u.re) :
    ∫ τ : ℝ, zetaIntegrand (W u₀ 0) g u a s τ =
      ((weightOneParam u₀).twist u a).archFactor s * zetaEnt u₀ 0 g u a s := by
  have hw := wvar_re_pos hs
  have hint : ∫ τ : ℝ, zetaIntegrand (W u₀ 0) g u a s τ = ∫ ρ : ℝ, halfLine u₀ 0 g u a s ρ := by
    rw [zetaIntegrand_eq_halfLine hg]
    rcases sgn_eq_one_or g with h | h
    · simp only [h, one_mul]
    · simp only [h, neg_one_mul]
      exact MeasureTheory.integral_neg_eq_self (halfLine u₀ 0 g u a s) MeasureTheory.volume
  rw [hint, integral_halfLine hg hw a, archFactor_twist_weightOneParam]
  unfold zetaEnt
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  rw [Gammaℂ_def, Complex.cpow_def_of_ne_zero h2π]
  have hE : Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * -wvar u₀ 0 u s) *
      Complex.exp (wvar u₀ 0 u s * (Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g))) =
      Complex.exp (-(wvar u₀ 0 u s * Complex.log (rate g))) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [mul_neg] at hE ⊢
  linear_combination (-(Complex.Gamma (wvar u₀ 0 u s) * zconst u₀ 0 a g)) * hE

private theorem functional_equation_weightOne (g : M₂) (u : ℂ) (a : ZMod 2) (s : ℂ) (hg : g.det ≠ 0) :
    zetaEnt u₀ 0 (weyl * g) (-(u + (weightOneParam u₀).centralExponent))
        (a + (weightOneParam u₀).centralSign) (1 - s) =
      ((weightOneParam u₀).twist u a).epsilonFactor * zetaEnt u₀ 0 g u a s := by
  rw [centralExponent_weightOneParam, centralSign_weightOneParam, epsilonFactor_twist_weightOneParam]
  unfold zetaEnt
  rw [wvar_dual, zconst_weyl_mul hg a, lconst_weyl_mul hg]
  set L := Complex.log (2 * (Real.pi : ℂ)) - Complex.log (rate g) with hL
  set w := wvar u₀ 0 u s with hw
  set β := (iy g : ℂ) + (ix g : ℂ) * I with hβ
  set β' := (iy g : ℂ) - (ix g : ℂ) * I with hβ'
  have hq := qq_pos hg
  have hq0 : (qq g : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqC : β' * β = (qq g : ℂ) := by
    rw [hβ, hβ']; unfold qq; push_cast; linear_combination (-(ix g : ℂ) ^ 2) * I_sq
  have hexp : Complex.exp ((((0 : ℕ) : ℂ) + 1 - w) * -L)
      = (sgn g : ℂ) ^ (0 + 1) * β' ^ (0 + 1) * Complex.exp (w * L) := by
    rw [← exp_neg_pow_lconst hg, ← Complex.exp_add]; congr 1; ring
  rw [hexp]
  have hs : (sgn g : ℂ) ^ (0 + 1) * (sgn g : ℂ) ^ (0 + 1) = 1 := by
    rw [← mul_pow, show (sgn g : ℂ) * (sgn g : ℂ) = 1 by
      have := sgn_sq g; rw [sq] at this; exact_mod_cast this, one_pow]
  have hbb : β ^ (0 + 1) * β' ^ (0 + 1) = (qq g : ℂ) ^ (0 + 1) := by
    rw [← mul_pow, mul_comm, hqC]
  have key : β ^ (0 + 1) * β' ^ (0 + 1) * ((sgn g : ℂ) ^ (0 + 1) * (sgn g : ℂ) ^ (0 + 1)) / (qq g : ℂ) ^ (0 + 1)
      = 1 := by
    rw [hbb, hs, mul_one, div_self (pow_ne_zero _ hq0)]
  calc (1 / 2 : ℂ) * (I ^ (0 + 1) * β ^ (0 + 1) / (qq g : ℂ) ^ (0 + 1) * (sgn g : ℂ) ^ (0 + 1) *
          zconst u₀ 0 a g) * ((sgn g : ℂ) ^ (0 + 1) * β' ^ (0 + 1) * Complex.exp (w * L))
        = I ^ (0 + 1) * ((1 / 2 : ℂ) * zconst u₀ 0 a g * Complex.exp (w * L)) *
            (β ^ (0 + 1) * β' ^ (0 + 1) * ((sgn g : ℂ) ^ (0 + 1) * (sgn g : ℂ) ^ (0 + 1)) /
              (qq g : ℂ) ^ (0 + 1)) := by ring
    _ = _ := by rw [key, mul_one]

end WeightOne

private def archDatumR_weightOneMember (u₀ : ℂ) : ArchDatumR (weightOneParam u₀) where
  W := W u₀ 0
  smooth := contDiffOn_asPi_W
  unip_law := fun x g => W_unip_mul x g
  central_law := fun _ g hz => W_smul_weightOne hz g
  zetaEntire := zetaEnt u₀ 0
  zetaEntire_differentiable := zetaEnt_differentiable
  zeta_abscissa := -(shift u₀ 0).re
  zeta_integrable := fun _ u a _ hg hs => zeta_integrable hg u a hs
  zeta_eq := fun _ u a _ hg hs => zeta_eq_weightOne hg u a hs
  functional_equation := functional_equation_weightOne
  zetaEntire_finiteOrder := zetaEnt_finiteOrder
  decay_top := decay_top
  decay_zero := decay_zero

end DiscreteFamily

open DiscreteFamily in

private theorem archDatumR_weightOneMember_W_one_ne_zero (u₀ : ℂ) :
    (archDatumR_weightOneMember u₀).W 1 ≠ 0 := by
  show W u₀ 0 1 ≠ 0
  have h1 : nsq (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [nsq]
  have hiy : iy (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [iy, h1]
  have hix : ix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by simp [ix, h1]
  have hkap : kap (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [kap, h1]
  unfold W
  rw [if_pos (by simp), hix, hiy, hkap, h1]
  simp [ArchR.psi, prof, detPow]

open DiscreteFamily in

private theorem exists_archDatumR_weightOne (u₀ : ℂ) :
    ∃ D : ArchDatumR (RealArchParam.principal u₀ 0 u₀ 1), ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 :=
  ⟨archDatumR_weightOneMember u₀, 1, by
    simpa using archDatumR_weightOneMember_W_one_ne_zero u₀⟩

private theorem exists_archDatumR_oddArtin :
    ∃ D : ArchDatumR RealArchParam.oddArtin, ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 :=
  exists_archDatumR_weightOne 0

end LanglandsTunnell.Converse

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "signEpsilon RealArchParam.epsilonFactor RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.centralExponent RealArchParam.centralSign RealArchParam.oddArtin RealArchParam.discrete RealArchParam.principal"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.psi ArchDatumR"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

noncomputable section

namespace DiscreteFamily

p2m_open "LanglandsTunnell.Converse.ArchR"

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

section SO2

variable (r : M₂) (h10 : r 1 0 = -r 0 1) (h11 : r 1 1 = r 0 0) (hab : r 0 0 ^ 2 + r 0 1 ^ 2 = 1)

include h10 h11 in
private theorem mul_so2_apply (x : M₂) (i : Fin 2) :
    (x * r) i 0 = x i 0 * r 0 0 - x i 1 * r 0 1 ∧ (x * r) i 1 = x i 0 * r 0 1 + x i 1 * r 0 0 := by
  constructor
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, h10]; ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, h11]

include h10 h11 hab in
private theorem so2_det : r.det = 1 := by
  rw [Matrix.det_fin_two, h10, h11]; linear_combination hab

include h10 h11 hab in
private theorem nsq_mul_so2 (x : M₂) : nsq (x * r) = nsq x := by
  obtain ⟨e0, e1⟩ := mul_so2_apply r h10 h11 x 1
  unfold nsq; rw [e0, e1]
  linear_combination (x 1 0 ^ 2 + x 1 1 ^ 2) * hab

include h10 h11 hab in
private theorem det_mul_so2 (x : M₂) : (x * r).det = x.det := by
  rw [Matrix.det_mul, so2_det r h10 h11 hab, mul_one]

include h10 h11 hab in
private theorem iy_mul_so2 (x : M₂) : iy (x * r) = iy x := by
  unfold iy; rw [det_mul_so2 r h10 h11 hab, nsq_mul_so2 r h10 h11 hab]

include h10 h11 hab in
private theorem ix_mul_so2 (x : M₂) : ix (x * r) = ix x := by
  obtain ⟨a0, a1⟩ := mul_so2_apply r h10 h11 x 0
  obtain ⟨b0, b1⟩ := mul_so2_apply r h10 h11 x 1
  unfold ix; rw [nsq_mul_so2 r h10 h11 hab, a0, a1, b0, b1]
  congr 1
  linear_combination (x 0 0 * x 1 0 + x 0 1 * x 1 1) * hab

include h10 h11 hab in
private theorem detPow_mul_so2 (u₀ : ℂ) (x : M₂) : detPow u₀ (x * r) = detPow u₀ x := by
  unfold detPow; rw [det_mul_so2 r h10 h11 hab]

include h10 h11 hab in
private theorem kap_mul_so2 (x : M₂) : kap (x * r) = (⟨r 0 0, r 0 1⟩ : ℂ) * kap x := by
  obtain ⟨b0, b1⟩ := mul_so2_apply r h10 h11 x 1
  unfold kap; rw [nsq_mul_so2 r h10 h11 hab, b0, b1, mul_div_assoc']
  congr 1
  apply Complex.ext <;> simp <;> ring

include h10 h11 hab in

private theorem W_mul_so2 (u₀ : ℂ) (k₀ : ℕ) (x : M₂) :
    W u₀ k₀ (x * r) = (⟨r 0 0, r 0 1⟩ : ℂ) ^ (k₀ + 1) * W u₀ k₀ x := by
  unfold W
  rw [det_mul_so2 r h10 h11 hab]
  split_ifs with h
  · rw [ix_mul_so2 r h10 h11 hab, iy_mul_so2 r h10 h11 hab, nsq_mul_so2 r h10 h11 hab,
      detPow_mul_so2 r h10 h11 hab, kap_mul_so2 r h10 h11 hab, mul_pow]
    ring
  · simp

end SO2

private def secM (z : UpperHalfPlane) : M₂ := !![z.im, z.re; 0, 1]

private theorem secM_det (z : UpperHalfPlane) : (secM z).det = z.im := by
  simp [secM, Matrix.det_fin_two_of]

private theorem nsq_secM (z : UpperHalfPlane) : nsq (secM z) = 1 := by simp [nsq, secM]
private theorem kap_secM (z : UpperHalfPlane) : kap (secM z) = 1 := by
  unfold kap; rw [nsq_secM]; simp [secM]
private theorem iy_secM (z : UpperHalfPlane) : iy (secM z) = z.im := by
  unfold iy; rw [nsq_secM, secM_det, div_one]
private theorem ix_secM (z : UpperHalfPlane) : ix (secM z) = z.re := by
  unfold ix; rw [nsq_secM]; simp [secM]

private theorem W_secM (u₀ : ℂ) (k₀ : ℕ) (z : UpperHalfPlane) :
    W u₀ k₀ (secM z) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) * ((z.im ^ pexp k₀ : ℝ) : ℂ) * exp (u₀ * (Real.log z.im : ℂ)) := by
  unfold W
  rw [secM_det, if_pos z.im_pos, ix_secM, iy_secM, kap_secM, nsq_secM]
  simp only [one_pow, mul_one, Real.sqrt_one, Complex.ofReal_one, detPow, secM_det, psi, prof]
  have hz : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im (z : ℂ)).symm
  have hsplit : 2 * (Real.pi : ℂ) * I * (z : ℂ) =
      2 * (Real.pi : ℂ) * I * (z.re : ℂ) + ((-(2 * Real.pi * z.im) : ℝ) : ℂ) := by
    rw [hz]; push_cast; ring_nf; rw [I_sq]; ring
  rw [hsplit, Complex.exp_add]
  push_cast
  ring

private theorem W_secM_normalised (u₀ : ℂ) (k₀ : ℕ) (z : UpperHalfPlane) :
    W u₀ k₀ (secM z) * ((|(secM z).det| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) * ((z.im ^ ((k₀ : ℝ) / 2 + 1 / 2) : ℝ) : ℂ) *
        exp (u₀ * (Real.log z.im : ℂ)) := by
  rw [W_secM, secM_det, abs_of_pos z.im_pos]
  have h : (z.im ^ pexp k₀ : ℝ) * z.im ^ (-(1 / 2 : ℝ)) = z.im ^ ((k₀ : ℝ) / 2 + 1 / 2) := by
    rw [← Real.rpow_add z.im_pos, pexp]; congr 1; ring
  rw [← h]; push_cast; ring

private theorem descent_one_zero (z : UpperHalfPlane) :
    ((z.im : ℝ) : ℂ)⁻¹ * (W 0 1 (secM z) * ((|(secM z).det| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) := by
  rw [W_secM_normalised]
  have h : ((1 : ℕ) : ℝ) / 2 + 1 / 2 = (1 : ℝ) := by norm_num
  rw [h, Real.rpow_one, zero_mul, Complex.exp_zero, mul_one]
  have hne : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  field_simp

private theorem descent_zero_zero (z : UpperHalfPlane) :
    ((z.im : ℝ) : ℂ)⁻¹ * (W 0 0 (secM z) * ((|(secM z).det| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) * ((z.im ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [W_secM_normalised]
  have h : ((0 : ℕ) : ℝ) / 2 + 1 / 2 = (1 / 2 : ℝ) := by norm_num
  rw [h, zero_mul, Complex.exp_zero, mul_one]
  have hpos := z.im_pos
  have hne : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hsplit : (z.im ^ (1 / 2 : ℝ) : ℝ) = z.im * z.im ^ (-(1 / 2 : ℝ)) := by
    rw [mul_comm, ← Real.rpow_add_one hpos.ne']; norm_num
  rw [hsplit]; push_cast
  field_simp

private theorem coe_iwasawaSectionGL (z : UpperHalfPlane) :
    ((AutomorphicForm.iwasawaSectionGL z : GL (Fin 2) ℝ) : M₂) = secM z := rfl

private theorem W_iwasawaSection (u₀ : ℂ) (k₀ : ℕ) (z : UpperHalfPlane) :
    W u₀ k₀ ((AutomorphicForm.iwasawaSectionGL z : GL (Fin 2) ℝ) : M₂) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) * ((z.im ^ pexp k₀ : ℝ) : ℂ) * exp (u₀ * (Real.log z.im : ℂ)) := by
  rw [coe_iwasawaSectionGL, W_secM]

private theorem descent_raw_zero_one (z : UpperHalfPlane) :
    ((z.im : ℝ) : ℂ)⁻¹ * W 0 1 ((AutomorphicForm.iwasawaSectionGL z : GL (Fin 2) ℝ) : M₂) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) * ((z.im ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [W_iwasawaSection, zero_mul, Complex.exp_zero, mul_one]
  have hpos := z.im_pos
  have hne : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hsplit : (z.im ^ pexp 1 : ℝ) = z.im * z.im ^ (1 / 2 : ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one hpos.ne', pexp]; norm_num
  rw [hsplit]; push_cast
  field_simp

private theorem descent_normalised_zero_one (z : UpperHalfPlane) :
    ((z.im : ℝ) : ℂ)⁻¹ * (W 0 1 ((AutomorphicForm.iwasawaSectionGL z : GL (Fin 2) ℝ) : M₂) *
        ((|(((AutomorphicForm.iwasawaSectionGL z : GL (Fin 2) ℝ) : M₂)).det| ^ (-(1 / 2 : ℝ)) : ℝ)
          : ℂ)) =
      exp (2 * (Real.pi : ℂ) * I * (z : ℂ)) := by
  rw [coe_iwasawaSectionGL]; exact descent_one_zero z

section Translate

variable (x : M₂) (z : UpperHalfPlane)

private def jz : ℂ := (x 1 0 : ℂ) * (z : ℂ) + (x 1 1 : ℂ)

private def mob : ℂ := ((x 0 0 : ℂ) * (z : ℂ) + (x 0 1 : ℂ)) / jz x z

private theorem mulSec_apply_10 : (x * secM z) 1 0 = x 1 0 * z.im := by
  simp [secM, Matrix.mul_apply, Fin.sum_univ_two]
private theorem mulSec_apply_11 : (x * secM z) 1 1 = x 1 0 * z.re + x 1 1 := by
  simp [secM, Matrix.mul_apply, Fin.sum_univ_two]
private theorem mulSec_apply_00 : (x * secM z) 0 0 = x 0 0 * z.im := by
  simp [secM, Matrix.mul_apply, Fin.sum_univ_two]
private theorem mulSec_apply_01 : (x * secM z) 0 1 = x 0 0 * z.re + x 0 1 := by
  simp [secM, Matrix.mul_apply, Fin.sum_univ_two]
private theorem mulSec_det : (x * secM z).det = x.det * z.im := by
  rw [Matrix.det_mul, secM_det]

private theorem normSq_jz : Complex.normSq (jz x z) = nsq (x * secM z) := by
  unfold jz nsq
  rw [mulSec_apply_10, mulSec_apply_11]
  have hz : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im (z : ℂ)).symm
  rw [hz]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem jz_ne_zero (hx : x.det ≠ 0) : jz x z ≠ 0 := by
  intro h
  have h1 := congrArg Complex.normSq h
  rw [normSq_jz, map_zero] at h1
  unfold nsq at h1
  rw [mulSec_apply_10, mulSec_apply_11] at h1
  have hc : x 1 0 * z.im = 0 := by nlinarith [sq_nonneg (x 1 0 * z.im), sq_nonneg (x 1 0 * z.re + x 1 1)]
  have hc0 : x 1 0 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact h
    · exact absurd h z.im_ne_zero
  have hd0 : x 1 1 = 0 := by rw [hc0] at h1; nlinarith
  apply hx
  rw [Matrix.det_fin_two, hc0, hd0]; ring

private theorem nsq_mulSec_pos (hx : x.det ≠ 0) : 0 < nsq (x * secM z) := by
  rw [← normSq_jz]; exact Complex.normSq_pos.mpr (jz_ne_zero x z hx)

private theorem kap_mul_sqrt (hx : x.det ≠ 0) :
    kap (x * secM z) * (Real.sqrt (nsq (x * secM z)) : ℂ) = (starRingEnd ℂ) (jz x z) := by
  unfold kap
  have hs : (Real.sqrt (nsq (x * secM z)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (nsq_mulSec_pos x z hx)).ne'
  rw [div_mul_cancel₀ _ hs, mulSec_apply_10, mulSec_apply_11]
  unfold jz
  have hz : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im (z : ℂ)).symm
  rw [hz]
  apply Complex.ext <;> simp

private theorem ix_add_iy_mul_I (hx : x.det ≠ 0) :
    (ix (x * secM z) : ℂ) + (iy (x * secM z) : ℂ) * I = mob x z := by
  have hj : jz x z ≠ 0 := jz_ne_zero x z hx
  have hn : nsq (x * secM z) ≠ 0 := (nsq_mulSec_pos x z hx).ne'
  have hnC : ((nsq (x * secM z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold mob
  rw [eq_div_iff hj]

  have hix : (ix (x * secM z) : ℂ) =
      (((x * secM z) 0 0 * (x * secM z) 1 0 + (x * secM z) 0 1 * (x * secM z) 1 1 : ℝ) : ℂ) /
        ((nsq (x * secM z) : ℝ) : ℂ) := by
    unfold ix; push_cast; ring
  have hiy : (iy (x * secM z) : ℂ) = (((x * secM z).det : ℝ) : ℂ) / ((nsq (x * secM z) : ℝ) : ℂ) := by
    unfold iy; push_cast; ring
  rw [hix, hiy, div_mul_eq_mul_div _ _ I, ← add_div, div_mul_eq_mul_div, div_eq_iff hnC]

  have hnsq : nsq (x * secM z) = (x 1 0 * z.im) ^ 2 + (x 1 0 * z.re + x 1 1) ^ 2 := by
    unfold nsq; rw [mulSec_apply_10, mulSec_apply_11]
  rw [mulSec_apply_00, mulSec_apply_01, mulSec_apply_10, mulSec_apply_11, mulSec_det, hnsq, Matrix.det_fin_two]
  unfold jz
  have hz : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im (z : ℂ)).symm
  rw [hz]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

private theorem psi_mul_prof_zero (hx : x.det ≠ 0) :
    psi (ix (x * secM z)) * (prof 0 (iy (x * secM z)) : ℂ) =
      (iy (x * secM z) : ℂ) * exp (2 * (Real.pi : ℂ) * I * mob x z) := by
  rw [← ix_add_iy_mul_I x z hx]
  unfold psi prof pexp
  simp only [Nat.cast_zero, zero_div, zero_add, Real.rpow_one]
  push_cast
  have : 2 * (Real.pi : ℂ) * I * ((ix (x * secM z) : ℂ) + (iy (x * secM z) : ℂ) * I) =
      2 * (Real.pi : ℂ) * I * (ix (x * secM z) : ℂ) + (-(2 * (Real.pi : ℂ) * (iy (x * secM z) : ℂ))) := by
    ring_nf; rw [I_sq]; ring
  rw [this, Complex.exp_add]
  ring

private theorem W_zero_zero_mul_secM (hx : 0 < x.det) :
    W 0 0 (x * secM z) = (x.det : ℂ) * (z.im : ℂ) * exp (2 * (Real.pi : ℂ) * I * mob x z) / jz x z := by
  have hx' : x.det ≠ 0 := hx.ne'
  have hj : jz x z ≠ 0 := jz_ne_zero x z hx'
  unfold W
  rw [mulSec_det, if_pos (mul_pos hx z.im_pos)]
  simp only [zero_add, pow_one, detPow, zero_mul, Complex.exp_zero, mul_one]
  rw [mul_assoc (psi _ * _), kap_mul_sqrt x z hx', psi_mul_prof_zero x z hx']

  have hiy : (iy (x * secM z) : ℂ) = (x.det : ℂ) * (z.im : ℂ) / (Complex.normSq (jz x z) : ℂ) := by
    unfold iy; rw [mulSec_det, normSq_jz]; push_cast; ring
  have hcj : (starRingEnd ℂ) (jz x z) ≠ 0 := fun h => hj (by simpa using congrArg (starRingEnd ℂ) h)
  rw [hiy, Complex.normSq_eq_conj_mul_self]
  field_simp

private theorem W_zero_zero_mul_secM_of_nonpos (hx : ¬ 0 < x.det) : W 0 0 (x * secM z) = 0 := by
  unfold W
  rw [mulSec_det, if_neg]
  intro h
  exact hx (pos_of_mul_pos_left h z.im_pos.le)

end Translate

private def descentFn (x : M₂) (w : ℂ) : ℂ :=
  (x.det : ℂ) * exp (2 * (Real.pi : ℂ) * I * (((x 0 0 : ℂ) * w + (x 0 1 : ℂ)) / ((x 1 0 : ℂ) * w + (x 1 1 : ℂ)))) /
    ((x 1 0 : ℂ) * w + (x 1 1 : ℂ))

private theorem descentFn_coe (x : M₂) (z : UpperHalfPlane) (hx : 0 < x.det) :
    ((z.im : ℝ) : ℂ)⁻¹ * W 0 0 (x * secM z) = descentFn x (z : ℂ) := by
  rw [W_zero_zero_mul_secM x z hx]
  unfold descentFn mob jz
  have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
  field_simp

private theorem differentiableAt_descentFn (x : M₂) (hx : x.det ≠ 0) (z : UpperHalfPlane) :
    DifferentiableAt ℂ (descentFn x) (z : ℂ) := by
  have hj : (x 1 0 : ℂ) * (z : ℂ) + (x 1 1 : ℂ) ≠ 0 := jz_ne_zero x z hx
  unfold descentFn
  have hden : DifferentiableAt ℂ (fun w : ℂ => (x 1 0 : ℂ) * w + (x 1 1 : ℂ)) (z : ℂ) := by fun_prop
  have hnum : DifferentiableAt ℂ (fun w : ℂ => (x 0 0 : ℂ) * w + (x 0 1 : ℂ)) (z : ℂ) := by fun_prop
  have hmob : DifferentiableAt ℂ
      (fun w : ℂ => ((x 0 0 : ℂ) * w + (x 0 1 : ℂ)) / ((x 1 0 : ℂ) * w + (x 1 1 : ℂ))) (z : ℂ) :=
    hnum.div hden hj
  have hexp : DifferentiableAt ℂ (fun w : ℂ => exp (2 * (Real.pi : ℂ) * I *
      (((x 0 0 : ℂ) * w + (x 0 1 : ℂ)) / ((x 1 0 : ℂ) * w + (x 1 1 : ℂ))))) (z : ℂ) :=
    (hmob.const_mul _).cexp
  exact (hexp.const_mul _).div hden hj

private theorem descent_mdifferentiable (x : M₂) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * W 0 0 (x * secM z) := by
  by_cases hx : 0 < x.det
  · have hfun : (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * W 0 0 (x * secM z)) =
        descentFn x ∘ (fun z : UpperHalfPlane => (z : ℂ)) := by
      funext z; exact descentFn_coe x z hx
    rw [hfun]
    intro z
    exact ((differentiableAt_descentFn x hx.ne' z).mdifferentiableAt).comp z
      (UpperHalfPlane.mdifferentiable_coe z)
  · have hfun : (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * W 0 0 (x * secM z)) = fun _ => 0 := by
      funext z; rw [W_zero_zero_mul_secM_of_nonpos x z hx, mul_zero]
    rw [hfun]
    exact mdifferentiable_const

end DiscreteFamily

namespace WeightOneMember

open DiscreteFamily AutomorphicForm

private theorem archWeightCharℝ_val (n : ℤ) (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ n r : ℂˣ) : ℂ) =
      (⟨((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0,
        ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩ : ℂ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

private theorem member_weight_matrix (r : rowIsometrySubgroup₀ ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) :
    (archDatumR_weightOneMember 0).W (x * ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
      ((archWeightCharℝ 1 r : ℂˣ) : ℂ) * (archDatumR_weightOneMember 0).W x := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ r.2
  show W 0 0 (x * ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = _ * W 0 0 x
  rw [W_mul_so2 _ h10 h11 hab 0 0 x, archWeightCharℝ_val]
  simp

private theorem member_weight (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ) :
    (archDatumR_weightOneMember 0).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((archWeightCharℝ 1 r : ℂˣ) : ℂ) * (archDatumR_weightOneMember 0).W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Units.val_mul]
  exact member_weight_matrix r (x : Matrix (Fin 2) (Fin 2) ℝ)

private theorem member_descent (x : GL (Fin 2) ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ *
        (archDatumR_weightOneMember 0).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hfun : (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ *
      (archDatumR_weightOneMember 0).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * W 0 0 ((x : Matrix (Fin 2) (Fin 2) ℝ) * secM z) := by
    funext z
    rw [Units.val_mul, coe_iwasawaSectionGL]
    rfl
  rw [hfun]
  exact descent_mdifferentiable (x : Matrix (Fin 2) (Fin 2) ℝ)

private theorem premises_at_weightOneMember :
    (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (archDatumR_weightOneMember 0).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          ((archWeightCharℝ 1 r : ℂˣ) : ℂ) * (archDatumR_weightOneMember 0).W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∀ x : GL (Fin 2) ℝ,
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            (archDatumR_weightOneMember 0).W
              ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨member_weight, member_descent⟩

end WeightOneMember

end

end LanglandsTunnell.Converse

open AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero.LanglandsTunnell LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero.LanglandsTunnell.Converse"

theorem solution :
    ∃ d : ArchDatumR RealArchParam.oddArtin,
      (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        d.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 1 r : ℂ) * d.W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      (∀ (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            d.W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∃ g : GL (Fin 2) ℝ, d.W g ≠ 0 :=
  ⟨DiscreteFamily.archDatumR_weightOneMember 0,
    WeightOneMember.premises_at_weightOneMember.1,
    WeightOneMember.premises_at_weightOneMember.2,
    1, by simpa using archDatumR_weightOneMember_W_one_ne_zero 0⟩

end S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero (solution)
