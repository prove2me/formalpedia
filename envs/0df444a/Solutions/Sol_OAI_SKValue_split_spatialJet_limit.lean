-- Prove2me | solution 1 for OAI.SKValue.split_spatialJet_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:08:25.423296+00:00
-- url     : https://prove2.me/submissions/4830f017-e93f-426a-bab9-ef456796ea8e

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_splitSmooth_tendsto

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_PredictableNormalizer
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_mean {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_id_gaussianReal]

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

lemma gaussian_second_moment {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, (Z ω)^2 ∂μ = 1 := by
  have hvar := hZ.variance_eq
  rw [variance_eq_integral hZ.aemeasurable, gaussian_mean hZ] at hvar
  simpa using hvar

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ColeHopfPDE
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_log_pde {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') {c h : ℝ} (hc : c≠0) (hh : 0<h)
    (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    HasDerivAt (fun r ↦ Real.log (heat r f x)/c)
      ((1/2 : ℝ)*(deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x +
        c*(deriv (fun y ↦ Real.log (heat h f y)/c) x)^2)) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := ((heat_time_hasDerivAt hf hf' hf'' hfg hf'g hf''g x hh).log (hp x)).div_const c
  rw [heat_log_spatial_second hf hf' hf'' hfg hf'g hf''g c h hp,
    heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hp x,hc]
  ring

lemma coleHopf_pde_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 < c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  let f := fun x ↦ Real.exp (c*ψ x)
  let f' := fun x ↦ Real.exp (c*ψ x)*(c*deriv ψ x)
  let f'' := fun x ↦ Real.exp (c*ψ x)*((c*deriv ψ x)^2+c*deriv (deriv ψ) x)
  have hψd := hψs.differentiable (by norm_num)
  have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ's.differentiable (by norm_num)
  have hψc := hψs.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ''c : Continuous (deriv (deriv ψ)) :=
    hψ's.continuous_deriv (by norm_num)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f,f',f'']
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ hc.le
  have hψ'b (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hf'g : ExpGrowth f' := hfg.mul_bounded hc.le (fun y ↦ by
    simpa only [abs_mul,abs_of_pos hc,mul_one] using
      mul_le_mul_of_nonneg_left (hψ'b y) hc.le)
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (R := c^2+c*K) (by positivity) (fun y ↦ by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_pos hc]
    have hsq : (c*deriv ψ y)^2 ≤ c^2 := by
      have h := sq_le_sq₀ (abs_nonneg (deriv ψ y)) zero_le_one |>.mpr (hψ'b y)
      rw [sq_abs] at h
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)]
    linarith [mul_le_mul_of_nonneg_left (hψ'' y) hc.le])
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ hc.le y (Real.sqrt h)).ne'
  have hd := heat_log_pde hfd hf'd (by dsimp [f'']; fun_prop) hfg hf'g hf''g hc.ne' hh hp x
  have heq (r : ℝ) : coleHopf c r ψ = fun y ↦ Real.log (heat r f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  simp_rw [heq]
  exact hd

lemma coleHopf_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · have hd (y : ℝ) := ((hψs.differentiable (by norm_num)) y).hasDerivAt
    have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
    have hd' (y : ℝ) := ((hψ's.differentiable (by norm_num)) y).hasDerivAt
    have hψ'g : ExpGrowth (deriv ψ) := ExpGrowth.of_bound zero_le_one (fun y ↦ by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y))
    have hψ''g := ExpGrowth.of_bound hK hψ''
    have heq (r : ℝ) : coleHopf 0 r ψ = heat r ψ := by funext y; simp [coleHopf]
    have h1 : deriv (heat h ψ)=heat h (deriv ψ) := by
      funext y
      exact (heat_spatial_hasDerivAt hd hψ's.continuous (ExpGrowth.lipschitz hψ) hψ'g y h).deriv
    have h2 : deriv (heat h (deriv ψ))=heat h (deriv (deriv ψ)) := by
      funext y
      exact (heat_spatial_hasDerivAt hd' (hψ's.continuous_deriv (by norm_num)) hψ'g hψ''g y h).deriv
    simpa only [heq,h1,h2,zero_mul,add_zero] using
      heat_time_hasDerivAt hd hd' (hψ's.continuous_deriv (by norm_num))
        (ExpGrowth.lipschitz hψ) hψ'g hψ''g x hh
  · exact coleHopf_pde_of_pos hψ hψs hK hψ'' hc hh x

lemma coleHopf_backward_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c b t : ℝ} (hc : 0 ≤ c) (ht : t<b) (x : ℝ) :
    HasDerivAt (fun s ↦ coleHopf c (b-s) ψ x)
      (-(1/2 : ℝ)*(deriv (deriv (coleHopf c (b-t) ψ)) x+
        c*(deriv (coleHopf c (b-t) ψ) x)^2)) t := by
  have hd := (coleHopf_pde hψ hψs hK hψ'' hc (sub_pos.mpr ht) x).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_sub]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_BoundedSmooth
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.expGrowth {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    ExpGrowth f := by
  obtain ⟨C,hC,hfC⟩ := hf.bound_zero
  exact ExpGrowth.of_bound hC hfC

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BetaBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set
open scoped Topology
namespace SKValue

lemma inv_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹=x^(-(1/2 : ℝ)) := by
  rw [Real.rpow_neg hx,Real.sqrt_eq_rpow]

lemma intervalIntegrable_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt s)⁻¹) volume a b := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) (r := -(1/2 : ℝ)) (by norm_num)).congr
  intro s hs
  exact (inv_sqrt_eq_rpow ((le_min ha hb).trans hs.1.le)).symm

lemma integral_inv_sqrt {d : ℝ} (hd : 0 ≤ d) :
    (∫ s in (0 : ℝ)..d, (Real.sqrt s)⁻¹) = 2*Real.sqrt d := by
  calc
    _ = ∫ s in (0 : ℝ)..d, s^(-(1/2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hd] at hs
      exact inv_sqrt_eq_rpow hs.1
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num))]
      norm_num [Real.sqrt_eq_rpow]
      ring

lemma intervalIntegrable_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (s-a))⁻¹) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_right a
  simpa only [zero_add,sub_add_cancel] using h

lemma intervalIntegrable_inv_sqrt_sub_left {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (b-s))⁻¹) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_left b
  simpa only [sub_sub_cancel,sub_zero] using h.symm

lemma integral_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt (s-a))⁻¹)=2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ ↦ (Real.sqrt s)⁻¹),sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma integral_inv_sqrt_sub_left {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt (b-s))⁻¹)=2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ (Real.sqrt s)⁻¹),sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma sqrtKernel_nonneg (a b s : ℝ) : 0 ≤ sqrtKernel a b s := by unfold sqrtKernel; positivity

lemma sqrtKernel_le_majorant {a b s : ℝ} (hab : a<b) (hs : s∈Icc a b) :
    sqrtKernel a b s ≤ sqrtMajorant a b s := by
  have hd := Real.sqrt_pos.mpr (sub_pos.mpr hab)
  have hD := Real.sq_sqrt (sub_nonneg.mpr hab.le)
  have hx := Real.sq_sqrt (sub_nonneg.mpr hs.1)
  have hy := Real.sq_sqrt (sub_nonneg.mpr hs.2)
  have hsx := Real.sqrt_nonneg (s-a)
  have hsy := Real.sqrt_nonneg (b-s)
  unfold sqrtKernel sqrtMajorant
  by_cases hsa : s=a
  · subst s
    simp only [sub_self,Real.sqrt_zero,inv_zero,zero_mul,zero_add]
    positivity
  by_cases hsb : s=b
  · subst s
    simp only [sub_self,Real.sqrt_zero,inv_zero,mul_zero,add_zero]
    positivity
  have hxpos := Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_le_of_ne hs.1 (Ne.symm hsa)))
  have hypos := Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_le_of_ne hs.2 hsb))
  have hc : 0 ≤ 2/Real.sqrt (b-a) := by positivity
  by_cases hm : (b-a)/2 ≤ s-a
  · have hsqrt : Real.sqrt (b-a) ≤ 2*Real.sqrt (s-a) := by nlinarith
    have hi : (Real.sqrt (s-a))⁻¹ ≤ 2/Real.sqrt (b-a) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hxpos hd]
      nlinarith
    calc
      _  ≤  (2/Real.sqrt (b-a))*(Real.sqrt (b-s))⁻¹ := mul_le_mul_of_nonneg_right hi (by positivity)
      _  ≤  _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hc
  · have hsqrt : Real.sqrt (b-a) ≤ 2*Real.sqrt (b-s) := by nlinarith
    have hi : (Real.sqrt (b-s))⁻¹ ≤ 2/Real.sqrt (b-a) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hypos hd]
      nlinarith
    calc
      _  ≤  (Real.sqrt (s-a))⁻¹*(2/Real.sqrt (b-a)) := mul_le_mul_of_nonneg_left hi (by positivity)
      _  ≤  _ := by nlinarith [mul_nonneg hc (inv_nonneg.mpr hsy)]

lemma sqrtMajorant_integrable {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (sqrtMajorant a b) volume a b :=
  ((intervalIntegrable_inv_sqrt_sub hab).add (intervalIntegrable_inv_sqrt_sub_left hab)).const_mul _

lemma sqrtKernel_integrable {a b : ℝ} (hab : a<b) :
    IntervalIntegrable (sqrtKernel a b) volume a b := by
  apply (sqrtMajorant_integrable hab.le).mono_fun'
  · exact (((measurable_id.sub_const a).sqrt.inv).mul
      ((measurable_const.sub measurable_id).sqrt.inv)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hab.le] at hs
    rw [Real.norm_eq_abs,abs_of_nonneg (sqrtKernel_nonneg a b s)]
    exact sqrtKernel_le_majorant hab ⟨hs.1.le,hs.2⟩

lemma sqrtKernel_integral_le_eight {a b : ℝ} (hab : a<b) :
    (∫ s in a..b, sqrtKernel a b s) ≤ 8 := by
  have hd := Real.sqrt_ne_zero'.mpr (sub_pos.mpr hab)
  calc
    _  ≤  ∫ s in a..b, sqrtMajorant a b s :=
      intervalIntegral.integral_mono_on hab.le (sqrtKernel_integrable hab)
        (sqrtMajorant_integrable hab.le) (fun s hs ↦ sqrtKernel_le_majorant hab hs)
    _ = (2/Real.sqrt (b-a))*(2*Real.sqrt (b-a)+2*Real.sqrt (b-a)) := by
      unfold sqrtMajorant
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
        (intervalIntegrable_inv_sqrt_sub hab.le) (intervalIntegrable_inv_sqrt_sub_left hab.le),
        integral_inv_sqrt_sub hab.le,integral_inv_sqrt_sub_left hab.le]
    _ = 8 := by field_simp; ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ParametricChain
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal ENNReal BigOperators Convex
namespace SKValue

theorem parametric_spatial_error
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

lemma hasDerivAt_parametric_comp {f fx : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {t a b : ℝ}
    (hd : HasDerivAt (fun s ↦ f s (φ t)) a t) (hφ : HasDerivAt φ b t)
    (hx : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,φ t), HasDerivAt (f p.1) (fx p.1 p.2) p.2)
    (hc : ContinuousAt (fun p : ℝ×ℝ ↦ fx p.1 p.2) (t,φ t)) :
    HasDerivAt (fun s ↦ f s (φ s)) (a+fx t (φ t)*b) t := by
  have hsp := parametric_spatial_error hφ.continuousAt tendsto_const_nhds
    (s := Set.univ) (seg := by simp) (f := f) (f' := fun s x ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (fx s x))
    (φ := (1 : ℝ →L[ℝ] ℝ).smulRight (fx t (φ t)))
    (df' := by
      rw [nhdsWithin_univ,←nhds_prod_eq]
      exact hx.mono (fun p hp ↦ hp.hasFDerivAt.hasFDerivWithinAt))
    (cf' := by
      rw [nhdsWithin_univ,←nhds_prod_eq]
      exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp hc)
  have hsmall := (hsp.trans_isBigO hφ.isBigO_sub).add
    (hd.isLittleO.add (hφ.isLittleO.const_mul_left (fx t (φ t))))
  apply HasDerivAt.of_isLittleO
  have heq : (fun s ↦ f s (φ s)-f s (φ t)-
      (1 : ℝ →L[ℝ] ℝ).smulRight (fx t (φ t)) (φ s-φ t) +
      ((f s (φ t)-f t (φ t)-(s-t) • a)+fx t (φ t)*(φ s-φ t-(s-t) • b))) =
      (fun s ↦ f s (φ s)-f t (φ t)-(s-t) • (a+fx t (φ t)*b)) := by
    funext s
    simp only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,smul_eq_mul]
    ring
  rw [heq] at hsmall
  exact hsmall

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_JetAlgebra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

namespace JetExpr

lemma uniform_bound {α : Type*} {R : ℕ → α → ℝ}
    (hR : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a, |R j a|≤C) (e : JetExpr) :
    ∃ C : ℝ, 0≤C ∧ ∀ a, |eval (fun j ↦ R j a) e|≤C := by
  induction e with
  | const c => exact ⟨|c|,abs_nonneg c,fun _ ↦ le_rfl⟩
  | coord j => exact hR j
  | add e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A+B,add_nonneg hA hB,fun a ↦ (abs_add_le _ _).trans (add_le_add (he a) (hf a))⟩
  | mul e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A*B,mul_nonneg hA hB,fun a ↦ by
      simpa only [eval,abs_mul] using mul_le_mul (he a) (hf a) (abs_nonneg _) hA⟩

end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatContinuity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_continuous {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ×ℝ ↦ coleHopf c p.1 ψ p.2) := by
  by_cases hc0 : c=0
  · simpa [SKValue.coleHopf,hc0] using heat_continuous hψ.continuous (ExpGrowth.lipschitz hψ)
  · have hH := heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)) (ExpGrowth.exp_lipschitz hψ hc)
    simpa only [coleHopf,ite_eq_right hc0,Function.comp_def,Pi.mul_apply] using
      (hH.log (fun p ↦ (lipschitz_exp_integral_pos hψ hc p.2 (Real.sqrt p.1)).ne')).div_const c

lemma SmoothTerminal.coleHopf_uniform_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  rcases hc.eq_or_lt with rfl | hc
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    refine ⟨C,hC,?_⟩
    intro h x
    rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv_jets]
    exact heat_bound hC hb h x
  · exact coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogHeatJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma nonneg_time_lipschitz {f g : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ h, 0<h → HasDerivAt f (g h) h)
    (hb : ∀ h, 0≤h → |g h|≤C) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |f s-f t|≤C* |s-t| := by
  wlog hst : s≤t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hf.continuousOn
    (fun r hr ↦ hd r (hs.trans_lt hr.1)) (hg.intervalIntegrable _ _)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (f := g) (C := |C|) (fun r hr ↦ by
      rw [uIoc_of_le hst] at hr
      simpa only [Real.norm_eq_abs] using
        (hb r (hs.trans hr.1.le)).trans (le_abs_self C))
  rw [he,Real.norm_eq_abs] at hb'
  simpa only [abs_of_nonneg hC,abs_sub_comm,mul_comm] using hb'

lemma SmoothTerminal.coleHopf_time_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ d : ℝ → ℝ → ℝ, Continuous (fun p : ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C : ℝ, 0≤C ∧ ∀ h x, |d h x|≤C) ∧
      ∀ h x, 0<h → HasDerivAt (fun r ↦ iteratedDeriv n (deriv (coleHopf c r ψ)) x) (d h x) h := by
  rcases hc.eq_or_lt with rfl | hc
  · let d := fun h x ↦ (1/2 : ℝ)*iteratedDeriv (n+3) (heat h ψ) x
    refine ⟨d,continuous_const.mul (heat_jet_continuous hψ.smooth hψ.growth _),?_,?_⟩
    · obtain ⟨C,hC,hb⟩ := hψ.jets.bound (n+2)
      refine ⟨C/2,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2),
        heat_iteratedDeriv hψ.smooth hψ.growth,show n+3=(n+2)+1 from rfl,iteratedDeriv_succ']
      linarith [heat_bound hC hb h x]
    · intro h x hh
      simpa only [coleHopf_zero_coeff,←iteratedDeriv_succ'] using heat_jet_time hψ.smooth hψ.growth (n+1) x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    let R := fun j (p : ℝ×ℝ) ↦ normalizedJet F j p.1 p.2
    let E := JetExpr.D JetExpr.σh (JetExpr.logGradientJet n)
    let d := fun h x ↦ c⁻¹*JetExpr.eval (fun j ↦ R j (h,x)) E
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hR : ∀ j, Continuous (R j) := fun j ↦ heat_normalizedJet_continuous hes hg hp j
    refine ⟨d,continuous_const.mul (JetExpr.continuous_eval hR E),?_,?_⟩
    · have hRb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ p, |R j p|≤C := by
        intro j
        obtain ⟨C,hC,hb⟩ := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc.le j
        exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
      obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hRb E
      refine ⟨|c⁻¹| * C,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb (h,x)) (abs_nonneg _)
    · intro h x hh
      simp_rw [coleHopf_gradient_jet_expr hψ hc]
      apply HasDerivAt.const_mul
      apply JetExpr.hasDerivAt_eval
      intro j
      simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x hh

lemma SmoothTerminal.coleHopf_jets_time_lipschitz {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s t x, 0 ≤ s → 0 ≤ t →
      |iteratedDeriv n (deriv (coleHopf c s ψ)) x-iteratedDeriv n (deriv (coleHopf c t ψ)) x|≤C* |s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := hψ.coleHopf_time_jets hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((hψ.coleHopf_joint_jets hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun h hh ↦ hd h x hh) (fun h _ ↦ hb h x) hs ht

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ deriv (coleHopf c r ψ) x)
      ((1/2 : ℝ)*deriv (deriv (deriv (coleHopf c h ψ))) x+
        c*(deriv (coleHopf c h ψ) x*deriv (deriv (coleHopf c h ψ)) x)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [coleHopf_zero_coeff,zero_mul,add_zero,show (3 : ℕ)=1+1+1 from rfl,
      iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using heat_jet_time hψ.smooth hψ.growth 1 x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hd := (heat_normalizedJet_time hes hg hp 1 x hh).const_mul c⁻¹
    have hj0 := congrFun (coleHopf_gradient_jet_expr hψ hc 0 h) x
    have hj1 := congrFun (coleHopf_gradient_jet_expr hψ hc 1 h) x
    have hj2 := congrFun (coleHopf_gradient_jet_expr hψ hc 2 h) x
    simp only [iteratedDeriv_zero,show (2 : ℕ)=1+1 from rfl,
      iteratedDeriv_succ,JetExpr.logGradientJet,JetExpr.D,JetExpr.σx,JetExpr.eval] at hj0 hj1 hj2
    convert! hd using 1
    · funext r
      rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc r]
    · rw [hj0,hj1,hj2]
      field_simp [hc.ne']
      ring

lemma integral_from_deriv_on_strip {T : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hg : ContinuousOn g (Icc (0 : ℝ) T))
    (hd : ∀ r∈Ioo (0 : ℝ) T, HasDerivAt f (g r) r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, g r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable g volume a b :=
    (hg.mono (by
      intro r hr
      rcases mem_uIcc.mp hr with hr | hr
      · exact ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩
      · exact ⟨hb.1.trans hr.1,hr.2.trans ha.2⟩)).intervalIntegrable
  have he {a : ℝ} (ha : a∈Icc (0 : ℝ) T) : ∫ r in (0 : ℝ)..a, g r=f a-f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1
      (hf.mono (Icc_subset_Icc le_rfl ha.2))
      (fun r hr ↦ hd r ⟨hr.1,hr.2.trans_le ha.2⟩) (hi ⟨le_rfl,ha.1.trans ha.2⟩ ha)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,ht.1.trans ht.2⟩ ht) (hi ht hs)
  rw [he hs,he ht] at hadd
  linarith

lemma SmoothTerminal.backward_jet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun t ↦ iteratedDeriv n (deriv (coleHopf c (T-t) ψ)) x) := by
  have hmap : Continuous (fun t : ℝ ↦ (T-t,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hj : Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (coleHopf c p.1 ψ)) p.2) :=
    hψ.coleHopf_joint_jets hc n
  convert hj.comp hmap using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma SmoothTerminal.backward_gradient_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (coleHopf c (T-t) ψ) x) := by
  simpa only [iteratedDeriv_zero] using hψ.backward_jet_continuous hc T 0 x

lemma SmoothTerminal.backward_curvature_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (coleHopf c (T-t) ψ)) x) := by
  simpa only [iteratedDeriv_one] using hψ.backward_jet_continuous hc T 1 x

lemma SmoothTerminal.backward_third_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (deriv (coleHopf c (T-t) ψ))) x) := by
  simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    using hψ.backward_jet_continuous hc T 2 x

lemma SmoothTerminal.backward_value_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ coleHopf c (T-t) ψ x) :=
  (coleHopf_continuous hψ.lipschitz hc).comp ((continuous_const.sub continuous_id).prodMk continuous_const)

lemma SmoothTerminal.backward_value_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    coleHopf c (T-s) ψ x-coleHopf c (T-t) ψ x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
      c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
    c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_curvature_continuous hc T x)).add
      (continuous_const.mul (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).pow 2)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ coleHopf c (T-r) ψ x) (-g r) r := by
    obtain ⟨K,hK,hb⟩ := hψ.jets.deriv.bound_zero
    have hd := coleHopf_backward_pde hψ.lipschitz
      (hψ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hK hb hc hr.2 x
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip
    (hψ.backward_value_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.backward_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    deriv (coleHopf c (T-s) ψ) x-deriv (coleHopf c (T-t) ψ) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
      c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
    c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_third_continuous hc T x)).add
      (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul (hψ.backward_curvature_continuous hc T x)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ deriv (coleHopf c (T-r) ψ) x) (-g r) r := by
    have hd := (coleHopf_gradient_pde hψ hc (sub_pos.mpr hr.2) x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip (hψ.backward_gradient_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.constant_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    SmoothEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) := by
  refine ⟨fun _ _ ↦ hψ.evolve hc _,fun x ↦ (hψ.backward_value_continuous hc T x).continuousOn,
    fun n x ↦ (hψ.backward_jet_continuous hc T n x).continuousOn,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.coleHopf_uniform_jets hc n
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := hψ.coleHopf_jets_time_lipschitz hc n
    refine ⟨L,hL,?_⟩
    intro s hs t ht x
    have he : |(T-s)-(T-t)|=|s-t| := by rw [sub_sub_sub_cancel_left,abs_sub_comm]
    simpa only [he] using hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
  · intro t ht s hs x
    exact hψ.backward_value_pde hc T ht hs x
  · intro t ht s hs x
    exact hψ.backward_gradient_pde hc T ht hs x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolveStrips
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.jet_joint {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ∃ L : ℝ, 0≤L ∧ ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |iteratedDeriv n (deriv (V s)) y-iteratedDeriv n (deriv (V t)) x|≤L*(|s-t|+|y-x|) := by
  obtain ⟨A,hA,ha⟩ := h.temporal n
  obtain ⟨B,hB,hb⟩ := h.bound (n+1)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro s hs t ht x y
  have hd := (h.slices t ht).jets.smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hl : LipschitzWith ⟨B,hB⟩ (iteratedDeriv n (deriv (V t))) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro z
    have hz := hb t ht z
    rw [iteratedDeriv_succ] at hz
    exact_mod_cast hz
  have hx := hl.dist_le_mul y x
  simp only [Real.dist_eq] at hx
  change |iteratedDeriv n (deriv (V t)) y-iteratedDeriv n (deriv (V t)) x|≤B*|y-x| at hx
  have hh := abs_sub_le (iteratedDeriv n (deriv (V s)) y)
    (iteratedDeriv n (deriv (V t)) y) (iteratedDeriv n (deriv (V t)) x)
  have ht := ha s hs t ht y
  nlinarith [mul_nonneg hA (abs_nonneg (y-x)),mul_nonneg hB (abs_nonneg (s-t))]

lemma SmoothEvolution.deriv_bound {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
    |deriv (V t) x|≤1 := by
  simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (h.slices t ht).lipschitz (x₀ := x)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionDifferentiation
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.jet_joint_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ContinuousOn (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL,hl⟩ := h.jet_joint n
  have hh : LipschitzOnWith ⟨2*L,by positivity⟩
      (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [Real.dist_eq,Prod.dist_eq]
    have hb := hl p.1 hp.1 q.1 hq.1 q.2 p.2
    change |iteratedDeriv n (deriv (V p.1)) p.2-iteratedDeriv n (deriv (V q.1)) q.2|≤
      (2*L)*max |p.1-q.1| |p.2-q.2|
    have hm1 := le_max_left |p.1-q.1| |p.2-q.2|
    have hm2 := le_max_right |p.1-q.1| |p.2-q.2|
    nlinarith
  exact hh.continuousOn

lemma SmoothEvolution.jet_joint_continuousAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T) (x : ℝ) :
    ContinuousAt (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (t,x) := by
  exact (h.jet_joint_continuousOn n (t,x) ⟨⟨ht.1.le,ht.2.le⟩,mem_univ x⟩).continuousAt
    (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)

lemma SmoothEvolution.gradient_time_hasDerivAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T)
    (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ deriv (V s) x)
      (-((1/2 : ℝ)*deriv (deriv (deriv (V t))) x+γ t*(deriv (V t) x*deriv (deriv (V t)) x))) t := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x)
  have hc0 : ContinuousOn (fun r ↦ deriv (V r) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_zero] using h.continuous_jet 0 x
  have hc1 : ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc2 : ContinuousOn (fun r ↦ deriv (deriv (deriv (V r))) x) (Icc (0 : ℝ) T) := by
    simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hti : t∈Icc (0 : ℝ) T := ⟨ht.1.le,ht.2.le⟩
  have hn := Icc_mem_nhds ht.1 ht.2
  have hgc : ContinuousAt g t :=
    (continuousAt_const.mul ((hc2 t hti).continuousAt hn)).add
      (hγ.mul (((hc0 t hti).continuousAt hn).mul ((hc1 t hti).continuousAt hn)))
  have hgm : StronglyMeasurableAtFilter g (𝓝 t) volume := by
    refine ⟨Icc (0 : ℝ) T,hn,?_⟩
    exact (aestronglyMeasurable_const.mul (hc2.aestronglyMeasurable measurableSet_Icc)).add
      (hm.aestronglyMeasurable.mul ((hc0.aestronglyMeasurable measurableSet_Icc).mul
        (hc1.aestronglyMeasurable measurableSet_Icc)))
  have hd := (hasDerivAt_const t (deriv (V t) x)).sub
    (intervalIntegral.integral_hasDerivAt_right (a := t) (b := t) (by simp) hgm hgc)
  simp only [zero_sub] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  have hh := h.gradient_pde t hti s hs x
  dsimp only [g,Pi.sub_apply] at *
  linarith

lemma SmoothEvolution.gradient_curve_hasDerivAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T)
    (hγ : ContinuousAt γ t) {φ : ℝ → ℝ} {b : ℝ} (hφ : HasDerivAt φ b t) :
    HasDerivAt (fun s ↦ deriv (V s) (φ s))
      (-((1/2 : ℝ)*deriv (deriv (deriv (V t))) (φ t)+
        γ t*(deriv (V t) (φ t)*deriv (deriv (V t)) (φ t)))+deriv (deriv (V t)) (φ t)*b) t := by
  apply hasDerivAt_parametric_comp (h.gradient_time_hasDerivAt hm ht hγ (φ t)) hφ
  · have he : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,φ t), p.1∈Icc (0 : ℝ) T :=
      continuousAt_fst.preimage_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    filter_upwards [he] with p hp
    exact ((h.slices p.1 hp).jets.smooth.differentiable
      (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) p.2).hasDerivAt
  · simpa only [iteratedDeriv_one] using h.jet_joint_continuousAt 1 ht (φ t)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma sqrt_difference_bound {δ u v : ℝ} (hδ : 0<δ) (hu : δ≤u) (hv : δ≤v) :
    |Real.sqrt u-Real.sqrt v|≤(Real.sqrt δ)⁻¹*|u-v| := by
  have hd := Real.sqrt_pos.mpr hδ
  have hu0 := hδ.le.trans hu
  have hv0 := hδ.le.trans hv
  have he : |u-v|=|Real.sqrt u-Real.sqrt v| * (Real.sqrt u+Real.sqrt v) := by
    rw [←abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),←abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hu0,Real.sq_sqrt hv0]
  have hh : Real.sqrt δ≤Real.sqrt u+Real.sqrt v := by
    linarith [Real.sqrt_le_sqrt hu,Real.sqrt_nonneg v]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hd).mpr
  rw [he]
  exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)

lemma SmoothEvolution.heat_gradient_derivative_integral {T a t : ℝ} {γ : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V) (hm : Measurable γ)
    (ha : 0≤a) (hat : a<t) (ht : t<T) (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ heat (s-a) (deriv (V s)) x)
      (∫ z, -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) ∂standardGaussian) t := by
  let q := (a+t)/2
  have haq : a<q := by dsimp [q]; linarith
  have hqt : q<t := by dsimp [q]; linarith
  have hq0 : 0≤q := ha.trans haq.le
  have hti : t∈Icc (0 : ℝ) T := ⟨ha.trans hat.le,ht.le⟩
  have hψ := (h.slices t hti).jets
  let F := fun s z ↦ deriv (V s) (x+Real.sqrt (s-a)*z)
  let F' := fun z ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a)))
  obtain ⟨L,hL,hl⟩ := h.jet_joint 0
  simp only [iteratedDeriv_zero] at hl
  let bd := fun z : ℝ ↦ L*(1+(Real.sqrt (q-a))⁻¹*|z|)
  have hbd : Integrable bd standardGaussian := by
    exact ((integrable_const 1).add (((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs.const_mul _)).const_mul L
  have hfc0 : Continuous (deriv (V t)) := hψ.smooth.continuous
  have hfc1 : Continuous (deriv (deriv (V t))) := hψ.deriv.smooth.continuous
  have hfc2 : Continuous (deriv (deriv (deriv (V t)))) := hψ.deriv.deriv.smooth.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (F' := F') (s := Icc q T) (bound := bd) (μ := standardGaussian)
    (Icc_mem_nhds hqt ht)
    (by
      filter_upwards [Icc_mem_nhds hqt ht] with s hs
      exact (((h.slices s ⟨hq0.trans hs.1,hs.2⟩).jets.smooth.continuous).comp (by fun_prop)).aestronglyMeasurable)
    (hψ.expGrowth.shift_integrable hψ.smooth.continuous.measurable x (Real.sqrt (t-a)))
    (by dsimp [F']; fun_prop) _ hbd _).2
  · filter_upwards [] with z
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    have hb := hl s ⟨hq0.trans hs.1,hs.2⟩ r ⟨hq0.trans hr.1,hr.2⟩
      (x+Real.sqrt (r-a)*z) (x+Real.sqrt (s-a)*z)
    have hsr := sqrt_difference_bound (sub_pos.mpr haq)
      (show q - a ≤ s - a by linarith [hs.1]) (show q - a ≤ r - a by linarith [hr.1])
    rw [sub_sub_sub_cancel_right] at hsr
    have he : |(x+Real.sqrt (s-a)*z)-(x+Real.sqrt (r-a)*z)|=
        |Real.sqrt (s-a)-Real.sqrt (r-a)| * |z| := by rw [add_sub_add_left_eq_sub,←sub_mul,abs_mul]
    rw [he] at hb
    simp only [Real.dist_eq,Real.coe_nnabs]
    change |F s z-F r z|≤|bd z| * |s-r|
    have hbd0 : 0 ≤ bd z := by dsimp [bd]; positivity
    rw [abs_of_nonneg hbd0]
    dsimp only [F,bd]
    have hmul := mul_le_mul_of_nonneg_right hsr (abs_nonneg z)
    nlinarith
  · filter_upwards [] with z
    have hs := ((Real.hasDerivAt_sqrt (sub_pos.mpr hat).ne').comp t
      ((hasDerivAt_id t).sub_const a)).mul_const z
    have hφ := hs.const_add x
    convert! h.gradient_curve_hasDerivAt hm ⟨ha.trans_lt hat,ht⟩ hγ hφ using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F,F']
    ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShiftedPairing
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SKValue

lemma integral_sq_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := integral_sq_le_integral_sq hab
  simp only [sq_abs] at h
  exact (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr h

end SKValue

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatKernelBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (n : ℕ) :
    BoundedSmooth (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma BoundedSmooth.heat_deriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (h : ℝ) :
    _root_.deriv (heat h f)=heat h (_root_.deriv f) := by
  simpa only [iteratedDeriv_one] using heat_iteratedDeriv hf.smooth
    (fun n ↦ (hf.iteratedDeriv n).expGrowth) h 1

lemma standardGaussian_abs_integral_le_one : (∫ z : ℝ, |z| ∂standardGaussian)≤1 := by
  have hl : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) standardGaussian := HasLaw.id
  have hh := integral_abs_le_sqrt_integral_sq (gaussian_memLp hl 2 (by norm_num))
  rw [gaussian_second_moment hl,Real.sqrt_one] at hh
  exact hh

lemma BoundedSmooth.heat_kernel_deriv_bound {f : ℝ → ℝ} (hf : BoundedSmooth f)
    {A h : ℝ} (hA : 0≤A) (hb : ∀ x, |f x|≤A) (hh : 0<h) (x : ℝ) :
    |_root_.deriv (heat h f) x|≤A/Real.sqrt h := by
  have hs := Real.sqrt_pos.mpr hh
  have hid := gaussian_scale_deriv_eq
    (fun y ↦ (hf.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
    hf.deriv.smooth.continuous hf.expGrowth hf.deriv.expGrowth x (Real.sqrt h)
  have hi := hf.expGrowth.shift_mul_integrable hf.smooth.continuous.measurable x (Real.sqrt h)
  have hz : Integrable (fun z : ℝ ↦ |z| * A) standardGaussian := by
    exact ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs.mul_const A
  have hb' : |∫ z, z*f (x+Real.sqrt h*z) ∂standardGaussian|≤A := by
    calc
      _ ≤ ∫ z, |z*f (x+Real.sqrt h*z)| ∂standardGaussian := abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, |z| * A ∂standardGaussian := by
        apply integral_mono_ae hi.abs hz
        filter_upwards [] with z
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
      _ = (∫ z : ℝ, |z| ∂standardGaussian)*A := integral_mul_const _ _
      _ ≤ A := by nlinarith [standardGaussian_abs_integral_le_one]
  rw [hf.heat_deriv]
  apply (le_div_iff₀ hs).mpr
  rw [hid,abs_mul,abs_of_pos hs] at hb'
  exact (mul_comm _ _).trans_le hb'

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_BurgersDerivative
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.heat_gradient_hasDerivAt {T a t : ℝ} {γ : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V) (hm : Measurable γ)
    (ha : 0≤a) (hat : a<t) (ht : t<T) (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ heat (s-a) (deriv (V s)) x)
      (-γ t * heat (t-a) (fun y ↦ deriv (V t) y * deriv (deriv (V t)) y) x) t := by
  have hψ := (h.slices t ⟨ha.trans hat.le,ht.le⟩).jets
  have hid := gaussian_scale_deriv_eq
    (fun y ↦ (hψ.deriv.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
    hψ.deriv.deriv.smooth.continuous hψ.deriv.expGrowth hψ.deriv.deriv.expGrowth x (Real.sqrt (t-a))
  have hI := hψ.deriv.deriv.expGrowth.shift_integrable
    hψ.deriv.deriv.smooth.continuous.measurable x (Real.sqrt (t-a))
  have hJ := (hψ.mul hψ.deriv).expGrowth.shift_integrable
    (hψ.smooth.continuous.mul hψ.deriv.smooth.continuous).measurable x (Real.sqrt (t-a))
  have hZ := hψ.deriv.expGrowth.shift_mul_integrable
    hψ.deriv.smooth.continuous.measurable x (Real.sqrt (t-a))
  have he : (∫ z, -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) ∂standardGaussian) =
      -γ t * heat (t-a) (fun y ↦ deriv (V t) y * deriv (deriv (V t)) y) x := by
    have heq (z : ℝ) : deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) =
        (2*Real.sqrt (t-a))⁻¹*(z*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)) := by ring
    simp_rw [heq]
    have hadd := integral_add ((hI.const_mul (1/2 : ℝ)).add (hJ.const_mul (γ t))).neg (hZ.const_mul ((2*Real.sqrt (t-a))⁻¹))
    simp only [Pi.neg_apply,Pi.add_apply] at hadd
    rw [hadd,integral_neg,integral_add (hI.const_mul (1/2 : ℝ)) (hJ.const_mul (γ t))]
    simp only [integral_const_mul]
    rw [hid]
    dsimp only [heat]
    field_simp [(Real.sqrt_pos.mpr (sub_pos.mpr hat)).ne']
    ring
  rw [←he]
  exact h.heat_gradient_derivative_integral hm ha hat ht hγ x

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma heat_family_continuousOn {T : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ F p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ))
    (hC : 0≤C) (hb : ∀ t∈Icc (0 : ℝ) T, ∀ x, |F t x|≤C) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (F t) x) (Icc (0 : ℝ) T) := by
  apply continuousOn_of_dominated (bound := fun _ ↦ |C|) (μ := standardGaussian)
  · intro t ht
    have hct : Continuous (F t) := by
      have hh : ContinuousOn (F t) univ := hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (MapsTo.prodMk (fun _ _ ↦ ht) (fun _ _ ↦ mem_univ _))
      simpa only [Function.comp_def,continuousOn_univ] using hh
    exact (hct.comp (by fun_prop)).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hb t ht (x+Real.sqrt (t-a)*z))
  · exact integrable_const |C|
  · filter_upwards [] with z
    exact hc.comp ((continuous_id.prodMk (by fun_prop)).continuousOn)
      (fun t ht ↦ ⟨ht,mem_univ _⟩)

lemma SmoothEvolution.heat_gradient_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (deriv (V t)) x) (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  simpa only [iteratedDeriv_zero] using heat_family_continuousOn (h.jet_joint_continuousOn 0) hC hb a x

lemma SmoothEvolution.heat_gradient_lipschitzOn {T a q b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (haq : a<q) (hqb : q≤b) (hb : b≤T) (x : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun t ↦ heat (t-a) (deriv (V t)) x) (Icc q b) := by
  obtain ⟨L,hL,hl⟩ := h.jet_joint 0
  simp only [iteratedDeriv_zero] at hl
  let C := L*(1+(Real.sqrt (q-a))⁻¹)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨⟨C,hC⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs r hr
  have hsub : Icc q b ⊆ Icc (0 : ℝ) T :=
    (Icc_subset_Icc_iff hqb).mpr ⟨ha.trans haq.le,hb⟩
  have hsT : s∈Icc (0 : ℝ) T := hsub hs
  have hrT : r∈Icc (0 : ℝ) T := hsub hr
  have hi (u : ℝ) (hu : u∈Icc (0 : ℝ) T) :
      Integrable (fun z ↦ deriv (V u) (x+Real.sqrt (u-a)*z)) standardGaussian :=
    (h.slices u hu).jets.expGrowth.shift_integrable (h.slices u hu).jets.smooth.continuous.measurable x _
  have hz : Integrable (fun z : ℝ ↦ |z|) standardGaussian :=
    ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs
  have hbd : Integrable (fun z : ℝ ↦ L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * |z|)) standardGaussian :=
    ((integrable_const _).add (hz.const_mul _)).const_mul L
  have hd : |heat (s-a) (deriv (V s)) x-heat (r-a) (deriv (V r)) x|≤C*|s-r| := by
    unfold heat
    rw [←integral_sub (hi s hsT) (hi r hrT)]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ z : ℝ, L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * |z|) ∂standardGaussian := by
        apply integral_mono_ae ((hi s hsT).sub (hi r hrT)).abs hbd
        filter_upwards [] with z
        have hh := hl s hsT r hrT (x+Real.sqrt (r-a)*z) (x+Real.sqrt (s-a)*z)
        have he : |(x+Real.sqrt (s-a)*z)-(x+Real.sqrt (r-a)*z)|=
          |Real.sqrt (s-a)-Real.sqrt (r-a)| * |z| := by rw [add_sub_add_left_eq_sub,←sub_mul,abs_mul]
        rw [he] at hh
        have hsr := sqrt_difference_bound (sub_pos.mpr haq)
          (show q-a ≤ s-a by linarith [hs.1]) (show q-a ≤ r-a by linarith [hr.1])
        rw [sub_sub_sub_cancel_right] at hsr
        have hh' := mul_le_mul_of_nonneg_right hsr (abs_nonneg z)
        simp only [Pi.sub_apply]
        exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hh') hL)
      _ = L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * (∫ z : ℝ, |z| ∂standardGaussian)) := by
        rw [integral_const_mul,integral_add (integrable_const _) (hz.const_mul _),integral_const,integral_const_mul]
        simp
      _ ≤ C*|s-r| := by
        have hh := mul_le_mul_of_nonneg_left standardGaussian_abs_integral_le_one
          (show 0≤L*((Real.sqrt (q-a))⁻¹*|s-r|) by positivity)
        dsimp [C]
        nlinarith
  change dist _ _ ≤ C*dist s r
  simpa only [Real.dist_eq] using hd

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BurgersMild
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma monotoneOn_ae_continuousAt_interior {T : ℝ} {γ : ℝ → ℝ}
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) :
    ∀ᵐ t : ℝ, t∈Ioo (0 : ℝ) T → ContinuousAt γ t := by
  filter_upwards [hγ.countable_not_continuousWithinAt.ae_notMem volume] with t ht hti
  have hc : ContinuousWithinAt γ (Icc (0 : ℝ) T) t := by
    by_contra hc
    exact ht ⟨⟨hti.1.le,hti.2.le⟩,hc⟩
  exact hc.continuousAt (Icc_mem_nhds hti.1 hti.2)

lemma SmoothEvolution.heat_nonlinearity_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y) x)
      (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  obtain ⟨D,hD,hd⟩ := h.bound 1
  simp only [iteratedDeriv_zero] at hb
  simp only [iteratedDeriv_one] at hd
  apply heat_family_continuousOn (C := C*D)
  · simpa only [iteratedDeriv_zero,iteratedDeriv_one,Pi.mul_def] using
      (h.jet_joint_continuousOn 0).mul (h.jet_joint_continuousOn 1)
  · positivity
  · intro t ht y
    rw [abs_mul]
    exact mul_le_mul (hb t ht y) (hd t ht y) (abs_nonneg _) hC

lemma SmoothEvolution.heat_gradient_interval {T a q b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (ha : 0≤a) (haq : a<q) (hqb : q≤b) (hb : b≤T) (x : ℝ) :
    heat (b-a) (deriv (V b)) x-heat (q-a) (deriv (V q)) x =
      -(∫ s in q..b, γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x) := by
  obtain ⟨L,hL⟩ := h.heat_gradient_lipschitzOn ha haq hqb hb x
  have hL' : LipschitzOnWith L (fun t ↦ heat (t-a) (deriv (V t)) x) (uIcc q b) := by
    simpa only [uIcc_of_le hqb] using hL
  rw [←hL'.absolutelyContinuousOnInterval.integral_deriv_eq_sub,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [monotoneOn_ae_continuousAt_interior hγ,(Set.countable_singleton b).ae_notMem volume] with s hs hsb hsi
  rw [uIoc_of_le hqb] at hsi
  have hst : s<T := (lt_of_le_of_ne hsi.2 (by simpa only [mem_singleton_iff] using hsb)).trans_le hb
  have has : a < s := haq.trans hsi.1
  have hd := h.heat_gradient_hasDerivAt hm ha has hst (hs ⟨ha.trans_lt has,hst⟩) x
  simpa only [neg_mul] using hd.deriv

lemma SmoothEvolution.burgers_mild {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    deriv (V a) x=heat (b-a) (deriv (V b)) x+
      ∫ s in a..b, γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have haT : a∈Icc (0 : ℝ) T := ⟨ha,hab.le.trans hb⟩
  have hT : 0≤T := ha.trans haT.2
  let g := fun s ↦ γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x
  have hg : IntervalIntegrable g volume a b := by
    apply (hi.mono_set ?_).mul_continuousOn
    · simpa only [uIcc_of_le hab.le] using
        (h.heat_nonlinearity_continuousOn a x).mono (Icc_subset_Icc ha hb)
    · simp only [uIcc_of_le hab.le,uIcc_of_le hT]
      exact Icc_subset_Icc ha hb
  have hF : Tendsto (fun q ↦ heat (q-a) (deriv (V q)) x) (𝓝[>] a) (𝓝 (deriv (V a) x)) := by
    have hh := (h.heat_gradient_continuousOn a x a haT).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hab) (fun s hs ↦ ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩))
    simpa only [sub_self,heat_zero] using hh.tendsto
  have hI : Tendsto (fun q ↦ ∫ s in q..b, g s) (𝓝[>] a) (𝓝 (∫ s in a..b, g s)) := by
    have hgI : IntegrableOn g (uIcc a b) volume := (intervalIntegrable_iff').mp hg
    have hh := (intervalIntegral.continuousOn_primitive_interval_left hgI a
      (by simp only [uIcc_of_le hab.le]; exact ⟨le_rfl,hab.le⟩)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hab) (by intro s hs; simpa only [uIcc_of_le hab.le] using ⟨hs.1.le,hs.2.le⟩))
    exact hh.tendsto
  have he : (fun q ↦ heat (q-a) (deriv (V q)) x) =ᶠ[𝓝[>] a]
      (fun q ↦ heat (b-a) (deriv (V b)) x+∫ s in q..b, g s) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with q hq
    have hh := h.heat_gradient_interval hm hγ ha hq.1 hq.2.le hb x
    change _ = -(∫ s in q..b, g s) at hh
    linarith
  exact tendsto_nhds_unique hF ((tendsto_const_nhds.add hI).congr' he.symm)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothFamily
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.gradient_family {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) : BoundedSmoothFamily T (fun t ↦ deriv (V t)) :=
  ⟨fun t ht ↦ (h.slices t ht).jets,h.bound,h.jet_joint_continuousOn⟩

lemma BoundedSmoothFamily.deriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) : BoundedSmoothFamily T (fun t ↦ _root_.deriv (F t)) := by
  refine ⟨fun t ht ↦ (h.slices t ht).deriv,?_,?_⟩
  · intro n
    simpa only [iteratedDeriv_succ'] using h.bound (n+1)
  · intro n
    simpa only [iteratedDeriv_succ'] using h.joint (n+1)

lemma BoundedSmoothFamily.mul {T : ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily T F) (hG : BoundedSmoothFamily T G) :
    BoundedSmoothFamily T (fun t x ↦ F t x*G t x) := by
  classical
  have hid (n : ℕ) (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
      iteratedDeriv n (fun x ↦ F t x*G t x) x =
      ∑ i∈Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i (F t) x*iteratedDeriv (n-i) (G t) x := by
    rw [iteratedDeriv_fun_mul
      ((hF.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
      ((hG.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
  refine ⟨fun t ht ↦ (hF.slices t ht).mul (hG.slices t ht),?_,?_⟩
  · intro n
    choose A hA hFA using hF.bound
    choose B hB hGB using hG.bound
    refine ⟨∑ i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i),?_,?_⟩
    · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))
    · intro t ht x
      rw [hid n t ht x]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFA i t ht x) (Nat.cast_nonneg _)) (hGB (n-i) t ht x)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
  · intro n
    apply ContinuousOn.congr (f := fun p : ℝ×ℝ ↦ ∑ i∈Finset.range (n+1),
      (n.choose i : ℝ)*iteratedDeriv i (F p.1) p.2*iteratedDeriv (n-i) (G p.1) p.2)
    · apply continuousOn_finsetSum
      intro i _
      simpa only [Pi.mul_def] using (continuousOn_const.mul (hF.joint i)).mul (hG.joint (n-i))
    · intro p hp
      exact hid n p.1 hp.1 p.2

lemma BoundedSmoothFamily.heat_continuousOn {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (F t) x) (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  simpa only [iteratedDeriv_zero] using heat_family_continuousOn (h.joint 0) hC hb a x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_DuhamelJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmoothFamily.duhamel_hasDerivAt {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    HasDerivAt (duhamel a b γ F) (duhamel a b γ (fun t ↦ _root_.deriv (F t)) x) x := by
  have hfi (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*heat (s-a) (F s) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.heat_continuousOn a u).mono (Icc_subset_Icc ha hb)
  have hf'i (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*heat (s-a) (_root_.deriv (F s)) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.deriv.heat_continuousOn a u).mono (Icc_subset_Icc ha hb)
  obtain ⟨C,hC,hbd⟩ := h.bound 1
  simp only [iteratedDeriv_one] at hbd
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u s ↦ γ s*heat (s-a) (F s) u)
    (F' := fun u s ↦ γ s*heat (s-a) (_root_.deriv (F s)) u)
    (s := univ) (bound := fun s ↦ |γ s| * C) (μ := volume.restrict (Ioc a b))
    univ_mem (Eventually.of_forall (fun u ↦ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi u)).aestronglyMeasurable))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi x))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hf'i x)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (heat_bound hC (hbd s ⟨ha.trans hs.1.le,hs.2.trans hb⟩) _ u) (abs_nonneg _))
    (hi'.abs.mul_const C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      have hfs := h.slices s ⟨ha.trans hs.1.le,hs.2.trans hb⟩
      exact (heat_spatial_hasDerivAt
        (fun y ↦ (hfs.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
        hfs.deriv.smooth.continuous hfs.expGrowth hfs.deriv.expGrowth u (s-a)).const_mul (γ s))
  change HasDerivAt (fun u ↦ ∫ s in a..b, γ s*heat (s-a) (F s) u)
    (∫ s in a..b, γ s*heat (s-a) (_root_.deriv (F s)) x) x
  simpa only [intervalIntegral.integral_of_le hab] using hd.2

lemma BoundedSmoothFamily.duhamel_deriv {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    _root_.deriv (duhamel a b γ F)=duhamel a b γ (fun t ↦ _root_.deriv (F t)) := by
  funext x
  exact (h.duhamel_hasDerivAt hi ha hab hb x).deriv

lemma BoundedSmoothFamily.iteratedDeriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (n : ℕ) :
    BoundedSmoothFamily T (fun t ↦ iteratedDeriv n (F t)) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma BoundedSmoothFamily.duhamel_iteratedDeriv {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (n : ℕ) :
    _root_.iteratedDeriv n (duhamel a b γ F)=duhamel a b γ (fun t ↦ _root_.iteratedDeriv n (F t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,(h.iteratedDeriv n).duhamel_deriv hi ha hab hb]
    simp only [iteratedDeriv_succ]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TimePatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_left {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : t≤a) :
    patchTime a f g t=f t := ite_eq_left ht
lemma patchTime_right {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : a<t) :
    patchTime a f g t=g (t-a) := ite_eq_right (not_le.mpr ht)

lemma patchTime_continuous {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) a)) (hg : ContinuousOn g (Icc (0 : ℝ) b))
    (hfg : f a=g 0) : ContinuousOn (patchTime a f g) (Icc (0 : ℝ) (a+b)) := by
  have hf' : ContinuousOn f (Icc (0 : ℝ) (a+b)∩closure (Iic a)) := by
    apply hf.mono
    simp only [closure_Iic]
    exact fun _ hx ↦ ⟨hx.1.1,hx.2⟩
  have hg' : ContinuousOn (fun t ↦ g (t-a)) (Icc (0 : ℝ) (a+b)∩closure (Iic a)ᶜ) := by
    apply hg.comp (continuous_id.sub continuous_const).continuousOn
    simp only [compl_Iic,closure_Ioi]
    intro t ht
    change 0≤t-a ∧ t-a≤b
    exact ⟨sub_nonneg.mpr ht.2,by linarith [ht.1.2]⟩
  have he : ∀ t∈Icc (0 : ℝ) (a+b)∩frontier (Iic a), f t=g (t-a) := by
    intro t ht
    have ht' : t=a := by simpa only [frontier_Iic,mem_singleton_iff] using ht.2
    subst t
    simpa only [sub_self] using hfg
  have hh := ContinuousOn.piecewise he hf' hg'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  simp only [patchTime,Set.piecewise,mem_Iic]

lemma patchTime_bound {a b C D : ℝ} (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ t∈Icc (0 : ℝ) a, |f t|≤C) (hg : ∀ t∈Icc (0 : ℝ) b, |g t|≤D) :
    ∀ t∈Icc (0 : ℝ) (a+b), |patchTime a f g t|≤C+D := by
  intro t ht
  by_cases hta : t≤a
  · rw [patchTime_left f g hta]
    exact (hf t ⟨ht.1,hta⟩).trans (le_add_of_nonneg_right hD)
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    exact (hg (t-a) ⟨by linarith,by linarith [ht.2]⟩).trans (le_add_of_nonneg_left hC)

lemma patchTime_lipschitz {a b C D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ s∈Icc (0 : ℝ) a, ∀ t∈Icc (0 : ℝ) a, |f s-f t|≤C*|s-t|)
    (hg : ∀ s∈Icc (0 : ℝ) b, ∀ t∈Icc (0 : ℝ) b, |g s-g t|≤D*|s-t|)
    (hfg : f a=g 0) :
    ∀ s∈Icc (0 : ℝ) (a+b), ∀ t∈Icc (0 : ℝ) (a+b),
      |patchTime a f g s-patchTime a f g t|≤(C+D)*|s-t| := by
  have hcross {s t : ℝ} (hs : s∈Icc (0 : ℝ) a) (ht : t∈Icc a (a+b)) :
      |f s-g (t-a)|≤(C+D)*|s-t| := by
    have h1 := hf s hs a ⟨ha,le_rfl⟩
    have h2 := hg 0 ⟨le_rfl,hb⟩ (t-a) ⟨sub_nonneg.mpr ht.1,by linarith [ht.2]⟩
    have hh := abs_sub_le (f s) (f a) (g (t-a))
    rw [hfg] at hh h1
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at h1
    rw [zero_sub,abs_neg,abs_of_nonneg (sub_nonneg.mpr ht.1)] at h2
    rw [abs_of_nonpos (sub_nonpos.mpr (hs.2.trans ht.1))]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ht.1),mul_nonneg hD (sub_nonneg.mpr hs.2)]
  intro s hs t ht
  by_cases hsa : s≤a <;> by_cases hta : t≤a
  · rw [patchTime_left f g hsa,patchTime_left f g hta]
    have hh := hf s ⟨hs.1,hsa⟩ t ⟨ht.1,hta⟩
    nlinarith [mul_nonneg hD (abs_nonneg (s-t))]
  · rw [patchTime_left f g hsa,patchTime_right f g (lt_of_not_ge hta)]
    exact hcross ⟨hs.1,hsa⟩ ⟨le_of_lt (lt_of_not_ge hta),ht.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_left f g hta,abs_sub_comm,abs_sub_comm s t]
    exact hcross ⟨ht.1,hta⟩ ⟨le_of_lt (lt_of_not_ge hsa),hs.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_right f g (lt_of_not_ge hta)]
    have hh := hg (s-a) ⟨by linarith,by linarith [hs.2]⟩ (t-a) ⟨by linarith,by linarith [ht.2]⟩
    rw [sub_sub_sub_cancel_right] at hh
    nlinarith [mul_nonneg hC (abs_nonneg (s-t))]

lemma patchTime_intervalIntegrable {a b : ℝ} (ha : 0≤a) (hb : 0≤b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 a) (hg : IntervalIntegrable g volume 0 b) :
    IntervalIntegrable (patchTime a f g) volume 0 (a+b) := by
  have hl : IntervalIntegrable (patchTime a f g) volume 0 a := by
    apply hf.congr_uIoo
    rw [uIoo_of_le ha]
    intro t ht
    exact (patchTime_left f g ht.2.le).symm
  have hr : IntervalIntegrable (fun t ↦ g (t-a)) volume a (a+b) := by
    simpa only [zero_add,add_comm b a] using hg.comp_sub_right a
  apply hl.trans
  apply hr.congr_uIoo
  rw [uIoo_of_le (le_add_of_nonneg_right hb)]
  intro t ht
  exact (patchTime_right f g ht.1).symm

lemma patchTime_integral_left {a s : ℝ} (hs : s∈Icc (0 : ℝ) a) (f g : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..s, patchTime a f g r)=∫ r in (0 : ℝ)..s, f r := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hs.1]
  exact fun r hr ↦ patchTime_left f g (hr.2.trans hs.2)

lemma patchTime_integral_right {a s : ℝ} (hs : a ≤ s) (f g : ℝ → ℝ) :
    (∫ r in a..s, patchTime a f g r)=∫ r in (0 : ℝ)..(s-a), g r := by
  calc
    _ = ∫ r in a..s, g (r-a) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hs
      exact fun r hr ↦ patchTime_right f g hr.1
    _ = _ := by rw [intervalIntegral.integral_comp_sub_right,sub_self]

lemma patchTime_primitive {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {f g p q : ℝ → ℝ} (hp : IntervalIntegrable p volume 0 a)
    (hq : IntervalIntegrable q volume 0 b)
    (hf : ∀ t∈Icc (0 : ℝ) a, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    (hg : ∀ t∈Icc (0 : ℝ) b, g t-g 0=∫ r in (0 : ℝ)..t, q r)
    (hfg : f a=g 0) : ∀ t∈Icc (0 : ℝ) (a+b),
    patchTime a f g t-patchTime a f g 0=∫ r in (0 : ℝ)..t, patchTime a p q r := by
  intro t ht
  rw [patchTime_left f g ha]
  by_cases hta : t≤a
  · rw [patchTime_left f g hta,patchTime_integral_left ⟨ht.1,hta⟩]
    exact hf t ⟨ht.1,hta⟩
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    have hi := patchTime_intervalIntegrable ha hb hp hq
    have hsub {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) :
        uIcc s t⊆uIcc (0 : ℝ) (a+b) := by
      rw [uIcc_of_le (add_nonneg ha hb)]
      exact uIcc_subset_Icc hs ht
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (hsub ⟨le_rfl,add_nonneg ha hb⟩ ⟨ha,le_add_of_nonneg_right hb⟩))
      (hi.mono_set (hsub ⟨ha,le_add_of_nonneg_right hb⟩ ht))
    rw [patchTime_integral_left ⟨ha,le_rfl⟩,patchTime_integral_right (le_of_lt (lt_of_not_ge hta))] at hh
    have h1 := hf a ⟨ha,le_rfl⟩
    have h2 := hg (t-a) ⟨by linarith,by linarith [ht.2]⟩
    linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_apply {a t x : ℝ} (V W : ℝ → ℝ → ℝ) :
    patchTime a V W t x=patchTime a (fun t ↦ V t x) (fun t ↦ W t x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_gradient {a t : ℝ} (V W : ℝ → ℝ → ℝ) :
    deriv (patchTime a V W t)=patchTime a (fun t ↦ deriv (V t)) (fun t ↦ deriv (W t)) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_jet {a t x : ℝ} (V W : ℝ → ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (deriv (patchTime a V W t)) x=
      patchTime a (fun t ↦ iteratedDeriv n (deriv (V t)) x) (fun t ↦ iteratedDeriv n (deriv (W t)) x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma SmoothEvolution.value_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+
      γ r*((1/2 : ℝ)*(deriv (V r) x)^2))) volume 0 T := by
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc1.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! continuousOn_const.mul (hc0.pow 2) using 1
  all_goals try with_reducible_and_instances rfl

lemma SmoothEvolution.gradient_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+
      γ r*(deriv (V r) x*deriv (deriv (V r)) x))) volume 0 T := by
  have hc2 : ContinuousOn (fun t ↦ deriv (deriv (deriv (V t))) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc2.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! hc0.mul hc1 using 1
  all_goals try with_reducible_and_instances rfl

lemma primitive_to_integral {T : ℝ} (hT : 0≤T) {f p : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 T)
    (hf : ∀ t∈Icc (0 : ℝ) T, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, p r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable p volume a b := hp.mono_set (by
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ha hb)
  have hh := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,hT⟩ ht) (hi ht hs)
  rw [←hf s hs,←hf t ht] at hh
  linarith

lemma SmoothEvolution.patch_value_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    patchTime a V W s x-patchTime a V W t x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (patchTime a V W r)) x+
      patchTime a γ η r*((1/2 : ℝ)*(deriv (patchTime a V W r) x)^2)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (W r)) x+η r*((1/2 : ℝ)*(deriv (W r) x)^2))
  have hp := hV.value_rhs_integrable ha hγ x
  have hq := hW.value_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, V t x-V 0 x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.value_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, W t x-W 0 x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.value_pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch_gradient_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    deriv (patchTime a V W s) x-deriv (patchTime a V W t) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (patchTime a V W r))) x+
      patchTime a γ η r*(deriv (patchTime a V W r) x*deriv (deriv (patchTime a V W r)) x)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (W r))) x+η r*(deriv (W r) x*deriv (deriv (W r)) x))
  have hp := hV.gradient_rhs_integrable ha hγ x
  have hq := hW.gradient_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, deriv (V t) x-deriv (V 0) x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.gradient_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, deriv (W t) x-deriv (W 0) x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.gradient_pde 0 ⟨le_rfl,hb⟩ t ht x
  have hj : deriv (V a) x=deriv (W 0) x := by rw [hjoin]
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw hj) hs ht
  simp_rw [patchTime_gradient,patchTime_apply]
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) :
    SmoothEvolution (a+b) (patchTime a γ η) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta : t≤a
    · rw [patchTime_left V W hta]
      exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)]
      exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro x
    simp_rw [patchTime_apply]
    exact patchTime_continuous (hV.continuous_value x) (hW.continuous_value x) (congrFun hjoin x)
  · intro n x
    simp_rw [patchTime_jet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_jet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_jet,patchTime_jet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_value_pde ha hb hW hγ hη hjoin hs ht x
  · intro t ht s hs x
    exact hV.patch_gradient_pde ha hb hW hγ hη hjoin hs ht x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_FiniteStepEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma profileTime_nonneg (l : HeatProfile) : 0≤profileTime l := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih => exact add_nonneg p.1.coe_nonneg ih

lemma profileCoeff_nonneg (l : HeatProfile) (t : ℝ) : 0≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons p l ih =>
    change 0≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact p.2.coe_nonneg
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

lemma profileCoeff_measurable (l : HeatProfile) : Measurable (profileCoeff l) := by
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    unfold profileCoeff patchTime
    exact Measurable.ite measurableSet_Iic measurable_const (ih.comp (measurable_id.sub measurable_const))

lemma SmoothTerminal.zero_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) :
    SmoothEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) := by
  refine ⟨fun _ _ ↦ hψ,fun _ ↦ continuousOn_const,fun _ _ ↦ continuousOn_const,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    exact ⟨C,hC,fun _ _ ↦ hb⟩
  · intro n
    exact ⟨0,le_rfl,by intros; simp⟩
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp

lemma SmoothTerminal.profile_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (l : HeatProfile) :
    SmoothEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) := by
  induction l with
  | nil => exact hψ.zero_evolution
  | cons p l ih =>
    have hv : SmoothTerminal (profileValue ψ l 0) := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hc := hv.constant_evolution p.2.coe_nonneg (p.1 : ℝ)
    apply hc.patch p.1.coe_nonneg (profileTime_nonneg l) ih intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,coleHopf_zero]

lemma patchTime_end {E : Type*} {a b : ℝ} (hb : 0≤b) {f g : ℝ → E} (hfg : f a=g 0) :
    patchTime a f g (a+b)=g b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa only [add_zero,patchTime_left f g le_rfl] using hfg
  · rw [patchTime_right f g (lt_add_of_pos_right a hb)]
    congr 1
    ring

lemma profileValue_terminal (ψ : ℝ → ℝ) (l : HeatProfile) :
    profileValue ψ l (profileTime l)=ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change patchTime _ _ _ ((p.1 : ℝ)+profileTime l)=ψ
    rw [patchTime_end (profileTime_nonneg l)]
    · exact ih
    · funext x
      simp only [sub_self,coleHopf_zero]

lemma profileCoeff_lower {l : HeatProfile} {c : ℝ}
    (hc : ∀ p∈l, c≤(p.2 : ℝ)) {t : ℝ} (ht : t∈Ioc (0 : ℝ) (profileTime l)) :
    c≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change c≤patchTime (p.1 : ℝ) _ _ t
    by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hta]
      exact hc p (by simp)
    · rw [patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih (fun q hq ↦ hc q (by simp [hq]))
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩

lemma profileCoeff_mono {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) :
    MonotoneOn (profileCoeff l) (Icc (0 : ℝ) (profileTime l)) := by
  induction l with
  | nil => intro s hs t ht hst; exact le_rfl
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    intro s hs t ht hst
    change patchTime (p.1 : ℝ) _ _ s≤patchTime (p.1 : ℝ) _ _ t
    by_cases hsa : s≤(p.1 : ℝ) <;> by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hsa,patchTime_left _ _ hta]
    · rw [patchTime_left _ _ hsa,patchTime_right _ _ (lt_of_not_ge hta)]
      apply profileCoeff_lower (fun q hq ↦ by exact_mod_cast hp q hq)
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
    · exact (hsa (hst.trans hta)).elim
    · rw [patchTime_right _ _ (lt_of_not_ge hsa),patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih hl
      · exact ⟨by linarith,by have hsu : s≤(p.1 : ℝ)+profileTime l := hs.2; linarith⟩
      · exact ⟨by linarith,by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
      · linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogCoshTerminal
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma logCoshTerminal_smooth (M : ℝ) : ContDiff ℝ ∞ (logCoshTerminal M) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))
  · intro x
    exact (mul_pos (by norm_num) (Real.cosh_pos (M*x))).ne'

lemma logCoshTerminal_hasDerivAt {M : ℝ} (hM : M≠0) (x : ℝ) :
    HasDerivAt (logCoshTerminal M) (Real.tanh (M*x)) x := by
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := ((hc.const_mul 2).log (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos (M*x))).ne').div_const M
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Function.comp_apply, mul_one]
  field_simp

lemma tanh_scaled_hasDerivAt (M x : ℝ) :
    HasDerivAt (fun x ↦ Real.tanh (M*x)) (M*(1-(Real.tanh (M*x))^2)) x := by
  have hs := (Real.hasDerivAt_sinh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := hs.div hc (Real.cosh_pos (M*x)).ne'
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Function.comp_apply, mul_one]
  field_simp [(Real.cosh_pos (M*x)).ne']

namespace JetExpr

lemma iteratedDeriv_fieldJet {R : ℕ → ℝ → ℝ} {σ : ℕ → JetExpr}
    (hd : ∀ j x, HasDerivAt (R j) (eval (fun i ↦ R i x) (σ j)) x) (e : JetExpr) (n : ℕ) :
    iteratedDeriv n (fun x ↦ eval (fun j ↦ R j x) e)=
      fun x ↦ eval (fun j ↦ R j x) (fieldJet σ e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (hasDerivAt_eval (fun j ↦ hd j x) _).deriv
end JetExpr

lemma logCoshTerminal_jets {M : ℝ} (hM : M≠0) :
    BoundedSmooth (deriv (logCoshTerminal M)) := by
  refine ⟨(contDiff_infty_iff_deriv.mp (logCoshTerminal_smooth M)).2,?_⟩
  intro n
  let σ : ℕ → JetExpr := fun _ ↦ JetExpr.mul (JetExpr.const M)
    (JetExpr.add (JetExpr.const 1) (JetExpr.mul (JetExpr.const (-1)) (JetExpr.mul (JetExpr.coord 0) (JetExpr.coord 0))))
  let R : ℕ → ℝ → ℝ := fun _ x ↦ Real.tanh (M*x)
  have hd : ∀ j x, HasDerivAt (R j) (JetExpr.eval (fun i ↦ R i x) (σ j)) x := by
    intro j x
    convert! tanh_scaled_hasDerivAt M x using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [σ,JetExpr.eval,R]
    ring
  have he : deriv (logCoshTerminal M)=fun x ↦ JetExpr.eval (fun j ↦ R j x) (JetExpr.coord 0) := by
    funext x
    exact (logCoshTerminal_hasDerivAt hM x).deriv
  rw [he,JetExpr.iteratedDeriv_fieldJet hd]
  exact JetExpr.uniform_bound (fun _ ↦ ⟨1,by norm_num,fun x ↦ (Real.abs_tanh_lt_one (M*x)).le⟩) _

lemma logCoshTerminal_smoothTerminal {M : ℝ} (hM : 0<M) : SmoothTerminal (logCoshTerminal M) := by
  have hs := logCoshTerminal_smooth M
  refine ⟨?_,hs,logCoshTerminal_jets hM.ne'⟩
  apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)))
  intro x
  have he := (logCoshTerminal_hasDerivAt hM.ne' x).deriv
  rw [he]
  exact_mod_cast (Real.abs_tanh_lt_one (M*x)).le

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GeneralProfileShape
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SKValue
lemma profileValue_zero_cons (A:ℝ → ℝ) (p:ℝ≥0 × ℝ≥0) (l:HeatProfile) :
    profileValue A (p::l) 0=coleHopf p.2 p.1 (profileValue A l 0) := by
  simp only [profileValue,patchTime_left _ _ p.1.coe_nonneg,sub_zero]
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_WeightedCap
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set
namespace SKValue

lemma weightedCap_bddAbove {a b C : ℝ} {F : ℝ → ℝ → ℝ} (_ : a≤b)
    (_ : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) :
    BddAbove ((fun p : ℝ×ℝ ↦ Real.sqrt (b-p.1)*|F p.1 p.2|) '' (Icc a b ×ˢ univ)) := by
  refine ⟨Real.sqrt (b-a)*C,?_⟩
  rintro _ ⟨⟨t,x⟩,ht,rfl⟩
  exact mul_le_mul (Real.sqrt_le_sqrt (sub_le_sub_left ht.1.1 b)) (hF t ht.1 x)
    (abs_nonneg _) (Real.sqrt_nonneg _)

lemma le_weightedCap {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) {t : ℝ} (ht : t∈Icc a b) (x : ℝ) :
    Real.sqrt (b-t)*|F t x|≤weightedCap a b F :=
  le_csSup (weightedCap_bddAbove hab hC hF) ⟨(t,x),⟨ht,mem_univ _⟩,rfl⟩

lemma weightedCap_nonneg {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) : 0≤weightedCap a b F := by
  simpa only [sub_self,Real.sqrt_zero,zero_mul] using le_weightedCap hab hC hF ⟨hab,le_rfl⟩ 0

lemma abs_le_weightedCap_div {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) {t : ℝ} (ht : t∈Ico a b) (x : ℝ) :
    |F t x|≤weightedCap a b F/Real.sqrt (b-t) := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))).mpr
  simpa only [mul_comm] using le_weightedCap hab hC hF ⟨ht.1,ht.2.le⟩ x

lemma weightedCap_le {a b A : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hF : ∀ t∈Icc a b, ∀ x, Real.sqrt (b-t)*|F t x|≤A) : weightedCap a b F≤A := by
  unfold weightedCap
  refine csSup_le ?_ ?_
  · exact ⟨Real.sqrt (b-a)*|F a 0|, ⟨(a,0),⟨⟨le_rfl,hab⟩,mem_univ _⟩,rfl⟩⟩
  · rintro _ ⟨⟨t,x⟩,ht,rfl⟩
    exact hF t ht.1 x

lemma weightedCap_absorb {a b A q C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) (hq : q≤1/2)
    (h : ∀ t∈Icc a b, ∀ x, Real.sqrt (b-t)*|F t x|≤A+q*weightedCap a b F) :
    weightedCap a b F≤2*A := by
  have hb := weightedCap_nonneg hab hC hF
  have hc := weightedCap_le hab h
  nlinarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_MildBurgersJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.heat_iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (h : ℝ) (n : ℕ) :
    _root_.iteratedDeriv n (heat h f)=heat h (_root_.iteratedDeriv n f) :=
  SKValue.heat_iteratedDeriv hf.smooth (fun n ↦ (hf.iteratedDeriv n).expGrowth) h n

lemma SmoothEvolution.burgers_jet_mild {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a≤b) (hb : b≤T) (m : ℕ) :
    iteratedDeriv (m+1) (deriv (V a)) =
      fun x ↦ deriv (heat (b-a) (iteratedDeriv m (deriv (V b)))) x+
        ∫ s in a..b, γ s*deriv (heat (s-a) (iteratedDeriv m
          (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y))) x := by
  have haT : a∈Icc (0 : ℝ) T := ⟨ha,hab.trans hb⟩
  have hbT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
  have hiab : IntervalIntegrable γ volume a b := hi.mono_set (by
    simp only [uIcc_of_le hab,uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb)
  have hF := h.gradient_family.mul h.gradient_family.deriv
  have hid : deriv (V a)=fun x ↦ heat (b-a) (deriv (V b)) x+
      duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y) x :=
    funext (h.burgers_mild hm hγ hi ha hab hb)
  have hdD (n : ℕ) : Differentiable ℝ (iteratedDeriv n
      (duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y))) := by
    rw [hF.duhamel_iteratedDeriv hiab ha hab hb]
    exact fun x ↦ ((hF.iteratedDeriv n).duhamel_hasDerivAt hiab ha hab hb x).differentiableAt
  have hcD : ContDiff ℝ ∞ (duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y)) :=
    (contDiff_iff_iteratedDeriv).mpr ⟨fun n _ ↦ (hdD n).continuous,fun n _ ↦ hdD n⟩
  have hfb := (h.slices b hbT).jets
  have hcH := SKValue.heat_contDiff hfb.smooth (fun n ↦ (hfb.iteratedDeriv n).expGrowth) (b-a)
  have horder := ENat.natCast_le_of_coe_top_le_withTop le_rfl (m+1)
  rw [hid]
  funext x
  rw [iteratedDeriv_fun_add (hcH.of_le horder).contDiffAt (hcD.of_le horder).contDiffAt]
  rw [hfb.heat_iteratedDeriv,hF.duhamel_iteratedDeriv hiab ha hab hb]
  rw [iteratedDeriv_succ,←(hfb.iteratedDeriv m).heat_deriv]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hs.1,hs.2.trans hb⟩
  dsimp only
  rw [iteratedDeriv_succ,←((hF.slices s hsT).iteratedDeriv m).heat_deriv]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ShortStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.jet_mild_bound {T a b Γ A K : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a<b) (hb : b≤T) (m : ℕ)
    (hΓ : 0≤Γ) (hA : 0≤A) (hK : 0≤K)
    (hγbd : ∀ s∈Icc a b, |γ s|≤Γ)
    (hprev : ∀ s∈Icc a b, ∀ x, |iteratedDeriv m (deriv (V s)) x|≤A)
    (hprod : ∀ s∈Icc a b, ∀ x,
      |iteratedDeriv m (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x|≤
        |iteratedDeriv (m+1) (deriv (V s)) x|+K)
    {t : ℝ} (ht : t∈Ico a b) (x : ℝ) :
    |iteratedDeriv (m+1) (deriv (V t)) x|≤A/Real.sqrt (b-t)+
      Γ*(8*weightedCap a b (fun s ↦ iteratedDeriv (m+1) (deriv (V s)))+2*K*Real.sqrt (b-t)) := by
  let F := fun s ↦ iteratedDeriv (m+1) (deriv (V s))
  let R := weightedCap a b F
  obtain ⟨C,hC,hbd⟩ := h.bound (m+1)
  have hbd' : ∀ s∈Icc a b, ∀ y, |F s y|≤C := fun s hs y ↦ hbd s ⟨ha.trans hs.1,hs.2.trans hb⟩ y
  have hR : 0≤R := weightedCap_nonneg hab.le hC hbd'
  have habT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab.le,hb⟩
  have htT : t∈Icc (0 : ℝ) T := ⟨ha.trans ht.1,ht.2.le.trans hb⟩
  let G := fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y
  let H := fun s ↦ γ s*deriv (heat (s-t) (iteratedDeriv m (G s))) x
  let J := fun s ↦ Γ*(R*sqrtKernel t b s+K*(Real.sqrt (s-t))⁻¹)
  have hg := h.gradient_family.mul h.gradient_family.deriv
  have hi' : IntervalIntegrable γ volume t b := hi.mono_set (by
    simp only [uIcc_of_le ht.2.le,uIcc_of_le (ha.trans (hab.le.trans hb))]
    exact Icc_subset_Icc htT.1 hb)
  have hHi : IntervalIntegrable H volume t b := by
    have hh := hi'.mul_continuousOn (show ContinuousOn
        (fun s ↦ heat (s-t) (iteratedDeriv (m+1) (G s)) x) (uIcc t b) from by
      simpa only [uIcc_of_le ht.2.le] using
        ((hg.iteratedDeriv (m+1)).heat_continuousOn t x).mono (Icc_subset_Icc htT.1 hb))
    apply hh.congr
    intro s hs
    rw [uIoc_of_le ht.2.le] at hs
    have hsT : s∈Icc (0 : ℝ) T := ⟨htT.1.trans hs.1.le,hs.2.trans hb⟩
    dsimp only [H,G]
    rw [iteratedDeriv_succ, ((hg.slices s hsT).iteratedDeriv m).heat_deriv]
  have hJi : IntervalIntegrable J volume t b :=
    (((sqrtKernel_integrable ht.2).const_mul R).add
      ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul K)).const_mul Γ
  have hpoint (s : ℝ) (hs : s∈Ioo t b) : |H s|≤J s := by
    have hsab : s∈Ico a b := ⟨ht.1.trans hs.1.le,hs.2⟩
    have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hsab.1,hs.2.le.trans hb⟩
    have hspos := Real.sqrt_pos.mpr (sub_pos.mpr hs.1)
    have hsbpos := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
    have hf := ((hg.slices s hsT).iteratedDeriv m).heat_kernel_deriv_bound
      (A := R/Real.sqrt (b-s)+K) (by positivity)
      (fun y ↦ (hprod s ⟨hsab.1,hsab.2.le⟩ y).trans
        (add_le_add (abs_le_weightedCap_div hab.le hC hbd' hsab y) le_rfl))
      (sub_pos.mpr hs.1) x
    dsimp only [H]
    rw [abs_mul]
    apply (mul_le_mul (hγbd s ⟨hsab.1,hsab.2.le⟩) hf (abs_nonneg _) hΓ).trans_eq
    dsimp only [J,sqrtKernel]
    ring
  have hint : |∫ s in t..b, H s|≤Γ*(8*R+2*K*Real.sqrt (b-t)) := by
    calc
      _ ≤ ∫ s in t..b, |H s| := intervalIntegral.abs_integral_le_integral_abs ht.2.le
      _ ≤ ∫ s in t..b, J s := intervalIntegral.integral_mono_on_of_le_Ioo ht.2.le hHi.abs hJi hpoint
      _ = Γ*(R*(∫ s in t..b, sqrtKernel t b s)+K*(2*Real.sqrt (b-t))) := by
        dsimp only [J]
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
          ((sqrtKernel_integrable ht.2).const_mul R) ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul K),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_inv_sqrt_sub ht.2.le]
      _ ≤ Γ*(R*8+K*(2*Real.sqrt (b-t))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (sqrtKernel_integral_le_eight ht.2) hR) le_rfl) hΓ
      _ = _ := by ring
  have hterm := ((h.slices b habT).jets.iteratedDeriv m).heat_kernel_deriv_bound hA
    (hprev b ⟨hab.le,le_rfl⟩) (sub_pos.mpr ht.2) x
  have hid := congrFun (h.burgers_jet_mild hm hγ hi htT.1 ht.2.le hb m) x
  change F t x=_+(∫ s in t..b, H s) at hid
  change |F t x|≤A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hterm hint)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShortStripClose
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma weighted_bound_algebra {a b t A Γ K R D : ℝ} (ht : t∈Ico a b)
    (hΓ : 0 ≤ Γ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hD : D ≤ A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))) :
    Real.sqrt (b-t)*D ≤ (A+2*Γ*K*(b-a))+(8*Γ*Real.sqrt (b-a))*R := by
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr ht.2)
  calc
    _  ≤  Real.sqrt (b-t)*(A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))) :=
      mul_le_mul_of_nonneg_left hD hs.le
    _ = A+2*Γ*K*(b-t)+(8*Γ*Real.sqrt (b-t))*R := by
      rw [mul_add,mul_comm (Real.sqrt (b-t)) (A/Real.sqrt (b-t)),div_mul_cancel₀ _ hs.ne']
      ring_nf
      rw [Real.sq_sqrt (sub_nonneg.mpr ht.2.le)]
      ring
    _  ≤  _ := by
      have hr := Real.sqrt_le_sqrt (sub_le_sub_left ht.1 b)
      have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) (by positivity : 0 ≤ 2*Γ*K)
      have h2 := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 8*Γ*R)
      nlinarith

lemma SmoothEvolution.short_strip_jet_bound {T a b Γ A K : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0 ≤ a) (hab : a<b) (hb : b ≤ T) (m : ℕ)
    (hΓ : 0 ≤ Γ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hγbd : ∀ s∈Icc a b, |γ s| ≤ Γ)
    (hprev : ∀ s∈Icc a b, ∀ x, |iteratedDeriv m (deriv (V s)) x| ≤ A)
    (hprod : ∀ s∈Icc a b, ∀ x,
      |iteratedDeriv m (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x| ≤
        |iteratedDeriv (m+1) (deriv (V s)) x|+K)
    (hshort : 8*Γ*Real.sqrt (b-a) ≤ 1/2) (x : ℝ) :
    |iteratedDeriv (m+1) (deriv (V a)) x| ≤ 2*(A+2*Γ*K*(b-a))/Real.sqrt (b-a) := by
  let F := fun s ↦ iteratedDeriv (m+1) (deriv (V s))
  obtain ⟨C,hC,hbd⟩ := h.bound (m+1)
  have hbd' : ∀ s∈Icc a b, ∀ y, |F s y| ≤ C := fun s hs y ↦ hbd s ⟨ha.trans hs.1,hs.2.trans hb⟩ y
  have hR := weightedCap_nonneg hab.le hC hbd'
  have hcap : weightedCap a b F ≤ 2*(A+2*Γ*K*(b-a)) := by
    apply weightedCap_absorb hab.le hC hbd' hshort
    intro t ht y
    rcases ht.2.eq_or_lt with rfl | htb
    · simp only [sub_self,Real.sqrt_zero,zero_mul]
      positivity
    · exact weighted_bound_algebra ⟨ht.1,htb⟩ hΓ hK hR
        (h.jet_mild_bound hm hγ hi ha hab hb m hΓ hA hK hγbd hprev hprod ⟨ht.1,htb⟩ y)
  apply (abs_le_weightedCap_div hab.le hC hbd' ⟨le_rfl,hab⟩ x).trans
  exact div_le_div_of_nonneg_right hcap (Real.sqrt_nonneg _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma lowerJetConstant_nonneg (m : ℕ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ lowerJetConstant m A := by
  unfold lowerJetConstant
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) hA)

lemma SmoothTerminal.product_jet_bound {f : ℝ → ℝ} (hf : SmoothTerminal f)
    (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ k ≤ m, ∀ x, |iteratedDeriv k (deriv f) x| ≤ A) (x : ℝ) :
    |iteratedDeriv m (fun y ↦ deriv f y*deriv (deriv f) y) x| ≤
      |iteratedDeriv (m+1) (deriv f) x|+lowerJetConstant m A := by
  have horder := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  rw [iteratedDeriv_fun_mul (hf.jets.smooth.of_le horder).contDiffAt
    (hf.jets.deriv.smooth.of_le horder).contDiffAt,Finset.sum_range_succ']
  have hstep (n : ℕ) : iteratedDeriv n (deriv (deriv f))=iteratedDeriv (n+1) (deriv f) :=
    (iteratedDeriv_succ').symm
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,iteratedDeriv_zero,Nat.sub_zero,hstep]
  apply (abs_add_le _ _).trans
  have hfirst : |deriv f x*iteratedDeriv (m+1) (deriv f) x| ≤
      |iteratedDeriv (m+1) (deriv f) x| := by
    rw [abs_mul]
    have hgrad := norm_deriv_le_of_lipschitz hf.lipschitz (x₀ := x)
    simp only [Real.norm_eq_abs,NNReal.coe_one] at hgrad
    nlinarith [abs_nonneg (iteratedDeriv (m+1) (deriv f) x)]
  have hrest : |∑ i∈Finset.range m, (m.choose (i+1) : ℝ)*iteratedDeriv (i+1) (deriv f) x*
      iteratedDeriv (m-(i+1)+1) (deriv f) x| ≤ lowerJetConstant m A := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (m.choose (i+1)))]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hb (i+1) (by omega) x) (Nat.cast_nonneg _))
      (hb (m-(i+1)+1) (by omega) x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
  exact (add_le_add hrest hfirst).trans_eq (add_comm _ _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma exists_short_length {Γ d : ℝ} (hΓ : 0 ≤ Γ) (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ δ ≤ d ∧ 8*Γ*Real.sqrt δ ≤ 1/2 := by
  let e := min (1 : ℝ) (min d (1/(16*(Γ+1))))
  have hden : 0<16*(Γ+1) := by positivity
  have he : 0<e := lt_min zero_lt_one (lt_min hd (one_div_pos.mpr hden))
  have he1 : e ≤ 1 := min_le_left _ _
  have hed : e ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hei : e ≤ 1/(16*(Γ+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hei' := (le_div_iff₀ hden).mp hei
  refine ⟨e^2,sq_pos_of_pos he,?_,?_⟩
  · nlinarith
  · rw [Real.sqrt_sq he.le]
    nlinarith

theorem uniform_bulk_jets (Γ : ℝ) (hΓ : 0 ≤ Γ) (T : ℝ) (m : ℕ) :
    ∀ S : ℝ, 0 ≤ S → S<T → ∃ A : ℝ, 0 ≤ A ∧
      ∀ (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ), SmoothEvolution T γ V → Measurable γ →
        MonotoneOn γ (Icc (0 : ℝ) T) → (∀ t∈Icc (0 : ℝ) T, |γ t| ≤ Γ) →
        ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ m, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A := by
  induction m with
  | zero =>
    intro S hS hST
    refine ⟨1,by norm_num,?_⟩
    intro γ V h hm hmono hbd t ht k hk x
    have hk' : k=0 := by omega
    subst k
    simpa only [iteratedDeriv_zero] using h.deriv_bound ⟨ht.1,ht.2.trans hST.le⟩ x
  | succ m ih =>
    intro S hS hST
    let S' := (S+T)/2
    have hSS' : S<S' := by dsimp only [S']; linarith
    have hS'T : S'<T := by dsimp only [S']; linarith
    obtain ⟨A,hA,hAall⟩ := ih S' (hS.trans hSS'.le) hS'T
    obtain ⟨δ,hδ,hδgap,hshort⟩ := exists_short_length hΓ (sub_pos.mpr hSS')
    let K := lowerJetConstant m A
    have hK : 0 ≤ K := lowerJetConstant_nonneg m hA
    let B := 2*(A+2*Γ*K*δ)/Real.sqrt δ
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨max A B,le_max_of_le_left hA,?_⟩
    intro γ V h hm hmono hbd t ht k hk x
    have hprev := hAall γ V h hm hmono hbd
    by_cases hkm : k ≤ m
    · exact (hprev t ⟨ht.1,ht.2.trans hSS'.le⟩ k hkm x).trans (le_max_left _ _)
    · have hk' : k=m+1 := by omega
      subst k
      have htδ : t<t+δ := by linarith
      have htδS' : t+δ ≤ S' := by linarith [ht.2]
      have hi : IntervalIntegrable γ volume 0 T := by
        apply MonotoneOn.intervalIntegrable
        simpa only [uIcc_of_le (hS.trans hST.le)] using hmono
      have hh := h.short_strip_jet_bound hm hmono hi ht.1 htδ (htδS'.trans hS'T.le) m
        hΓ hA hK
        (fun s hs ↦ hbd s ⟨ht.1.trans hs.1,hs.2.trans (htδS'.trans hS'T.le)⟩)
        (fun s hs y ↦ hprev s ⟨ht.1.trans hs.1,hs.2.trans htδS'⟩ m le_rfl y)
        (fun s hs y ↦ (h.slices s ⟨ht.1.trans hs.1,hs.2.trans (htδS'.trans hS'T.le)⟩).product_jet_bound
          m hA (fun j hj z ↦ hprev s ⟨ht.1.trans hs.1,hs.2.trans htδS'⟩ j hj z) y)
        (by simpa only [add_sub_cancel_left] using hshort) x
      have hh' : |iteratedDeriv (m+1) (deriv (V t)) x| ≤ B := by
        simpa only [add_sub_cancel_left] using hh
      exact hh'.trans (le_max_right _ _)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_UniformPolynomial
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
lemma BoundedUniformLimit.seq {A:Type*} {c:ℕ → ℝ} {d:ℝ}
    (hl:Tendsto c atTop (𝓝 d)) (hb:∃ C:ℝ,0 ≤ C ∧ ∀ n,|c n| ≤ C) :
    BoundedUniformLimit (fun n (_:A) ↦ c n) (fun _ ↦ d) := by
  obtain ⟨C,hC,hb⟩:=hb
  refine ⟨?_,C,hC,fun n _ ↦ hb n,fun _ ↦ le_of_tendsto hl.abs (Eventually.of_forall hb)⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  exact (Metric.tendsto_nhds.mp hl ε hε).mono (fun n hn _ ↦ by simpa only [dist_comm] using hn)
lemma BoundedUniformLimit.mul {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x*G n x) (fun x ↦ f x*g x) := by
  obtain ⟨C,hC,hb,hf⟩:=hF.bound
  obtain ⟨D,hD,hd,hg⟩:=hG.bound
  refine ⟨?_,C*D,mul_nonneg hC hD,?_,?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    let δ:=ε/(C+D+1)
    have hden:0<C+D+1 := by linarith
    have hδ:0<δ := div_pos hε hden
    have heq:δ*(C+D+1)=ε := div_mul_cancel₀ ε hden.ne'
    filter_upwards [(Metric.tendstoUniformly_iff.mp hF.tendsto) δ hδ,
      (Metric.tendstoUniformly_iff.mp hG.tendsto) δ hδ] with n hn hm x
    have hn':|F n x-f x|<δ := by simpa only [Real.dist_eq,abs_sub_comm] using hn x
    have hm':|G n x-g x|<δ := by simpa only [Real.dist_eq,abs_sub_comm] using hm x
    rw [Real.dist_eq,abs_sub_comm]
    have he:F n x*G n x-f x*g x=F n x*(G n x-g x)+(F n x-f x)*g x := by ring
    rw [he]
    apply (abs_add_le _ _).trans_lt
    rw [abs_mul,abs_mul]
    have h1:=mul_le_mul (hb n x) hm'.le (abs_nonneg _) hC
    have h2:=mul_le_mul hn'.le (hg x) (abs_nonneg _) hδ.le
    nlinarith
  · intro n x;rw [abs_mul];exact mul_le_mul (hb n x) (hd n x) (abs_nonneg _) hC
  · intro x;rw [abs_mul];exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hC
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_DerivativeLimit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue

lemma second_order_remainder {f : ℝ → ℝ} {C : ℝ} (hf : ContDiff ℝ 2 f) (hC : 0 ≤ C)
    (hb : ∀ x, |deriv (deriv f) x| ≤ C) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d| ≤ (C/2)*d^2 := by
  by_cases hd : d=0
  · rw [hd, add_zero, mul_zero, sub_self, sub_zero, abs_zero]
    exact mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg 0)
  have hne : x≠x+d := by intro hx; apply hd; linarith
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x=deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc,iteratedDeriv_one]
  have ht : taylorWithinEval f 1 (uIcc x (x+d)) x (x+d)=f x+deriv f x*d := by
    rw [taylorWithinEval_succ,taylor_within_zero_eval,h1]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf.contDiffOn
  rw [ht] at hy
  have he : f (x+d)-f x-deriv f x*d=deriv (deriv f) y*d^2/2 := by
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] at hy
    convert hy using 1 <;> ring
  rw [he,abs_div,abs_mul,abs_of_nonneg (sq_nonneg d)]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right (hb y) (sq_nonneg d)]

lemma derivative_difference_of_values {f g : ℝ → ℝ} {C ε d : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hC : 0 ≤ C) (hd : 0<d)
    (hfb : ∀ x, |deriv (deriv f) x| ≤ C) (hgb : ∀ x, |deriv (deriv g) x| ≤ C)
    (he : ∀ x, |f x-g x|<ε) (x : ℝ) :
    |deriv f x-deriv g x| * d < 2*ε+C*d^2 := by
  have hf' := second_order_remainder hf hC hfb x d
  have hg' := second_order_remainder hg hC hgb x d
  have hid : (deriv f x-deriv g x)*d=
      (f (x+d)-g (x+d))-(f x-g x)-
        (f (x+d)-f x-deriv f x*d)+(g (x+d)-g x-deriv g x*d) := by ring
  have hmul : |deriv f x-deriv g x| * d = |(deriv f x-deriv g x)*d| := by rw [abs_mul,abs_of_pos hd]
  rw [hmul,hid]
  have hp := abs_sub (f (x+d)-g (x+d)) (f x-g x)
  have hq := abs_sub ((f (x+d)-g (x+d))-(f x-g x)) (f (x+d)-f x-deriv f x*d)
  have hb := abs_add_le ((f (x+d)-g (x+d))-(f x-g x)-(f (x+d)-f x-deriv f x*d))
    (g (x+d)-g x-deriv g x*d)
  have h1 := he (x+d)
  have h2 := he x
  nlinarith

lemma uniform_derivative_limit {A : Type*} {F : ℕ → A → ℝ → ℝ} {f : A → ℝ → ℝ} {C : ℝ}
    (hF : TendstoUniformly (fun n (p : A×ℝ) ↦ F n p.1 p.2) (fun p ↦ f p.1 p.2) atTop)
    (hs : ∀ n a, ContDiff ℝ 2 (F n a)) (hC : 0 ≤ C)
    (hb : ∀ n a x, |deriv (deriv (F n a)) x| ≤ C) :
    TendstoUniformly (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2)
      (fun p ↦ deriv (f p.1) p.2) atTop ∧ ∀ a, Differentiable ℝ (f a) := by
  have hc : UniformCauchySeqOn (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2) atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let d := ε/(2*(C+1))
    have hd : 0<d := by dsimp [d]; positivity
    have hdC : C*d<ε/2 := by
      dsimp [d]
      have hn : 0<2*(C+1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hn).mpr
      nlinarith
    have hcF := (hF.tendstoUniformlyOn (s := univ)).uniformCauchySeqOn
    obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcF (ε*d/4) (by positivity)
    refine ⟨N,?_⟩
    intro m hm n hn p hp
    have he : ∀ x, |F m p.1 x-F n p.1 x|<ε*d/4 := by
      intro x
      simpa only [Real.dist_eq] using hN m hm n hn (p.1,x) (mem_univ _)
    have hv := derivative_difference_of_values (hs m p.1) (hs n p.1) hC hd
      (hb m p.1) (hb n p.1) he p.2
    rw [Real.dist_eq]
    have hh : |deriv (F m p.1) p.2-deriv (F n p.1) p.2| * d<ε*d := by
      nlinarith [mul_lt_mul_of_pos_right hdC hd]
    nlinarith
  have hex (p : A×ℝ) : ∃ g : ℝ, Tendsto (fun n ↦ deriv (F n p.1) p.2) atTop (𝓝 g) :=
    cauchySeq_tendsto_of_complete (hc.cauchySeq (mem_univ p))
  choose g hg using hex
  have hG : TendstoUniformly (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2) g atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun p _ ↦ hg p)
  have hgder (a : A) (x : ℝ) : HasDerivAt (f a) (g (a,x)) x := by
    apply hasDerivAt_of_tendstoUniformly (hG.comp (fun z ↦ (a,z)))
    · exact Eventually.of_forall (fun n y ↦ ((hs n a).differentiable (by norm_num) y).hasDerivAt)
    · intro y
      exact hF.tendsto_at (a,y)
  have heq : g=(fun p ↦ deriv (f p.1) p.2) := by
    funext p
    exact (hgder p.1 p.2).deriv.symm
  exact ⟨heq ▸ hG,fun a x ↦ (hgder a x).differentiableAt⟩

lemma contDiff_infty_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k hk =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp hk).2

lemma uniform_all_derivative_limits {A : Type*} {F : ℕ → A → ℝ → ℝ} {f : A → ℝ → ℝ}
    (hF : TendstoUniformly (fun n (p : A×ℝ) ↦ F n p.1 p.2) (fun p ↦ f p.1 p.2) atTop)
    (hs : ∀ n a, ContDiff ℝ ∞ (F n a))
    (hb : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ n a x, |iteratedDeriv (k+1) (F n a) x| ≤ C) :
    (∀ k, TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
      (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop) ∧ ∀ a, ContDiff ℝ ∞ (f a) := by
  have step (k : ℕ)
      (hk : TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
        (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop) :
      TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv (k+1) (F n p.1) p.2)
        (fun p ↦ iteratedDeriv (k+1) (f p.1) p.2) atTop ∧
        ∀ a, Differentiable ℝ (iteratedDeriv k (f a)) := by
    obtain ⟨C,hC,hbc⟩ := hb (k+1)
    have hh := uniform_derivative_limit (F := fun n a ↦ iteratedDeriv k (F n a))
      (f := fun a ↦ iteratedDeriv k (f a)) hk
      (fun n a ↦ (contDiff_infty_iteratedDeriv (hs n a) k).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC (fun n a x ↦ by
          simpa only [iteratedDeriv_succ] using hbc n a x)
    simpa only [iteratedDeriv_succ] using hh
  have hc : ∀ k, TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
      (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hF
    | succ k hk => exact (step k hk).1
  refine ⟨hc,?_⟩
  intro a
  apply contDiff_iff_iteratedDeriv.mpr
  constructor
  · intro m hm
    exact ((step m (hc m)).2 a).continuous
  · intro m hm
    exact (step m (hc m)).2 a

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridProfile
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma gridProfile_time (d : ℝ≥0) (f : ℕ → ℝ≥0) (j n : ℕ) :
    profileTime (gridProfile d f j n)=(n : ℝ)*d := by
  induction n generalizing j with
  | zero => simp only [gridProfile,profileTime,Nat.cast_zero,zero_mul]
  | succ n ih => simp only [gridProfile,profileTime,ih,Nat.cast_add,Nat.cast_one]; ring

lemma gridProfile_mem {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ} {p : ℝ≥0 × ℝ≥0}
    (hp : p∈gridProfile d f j n) : ∃ i, j ≤ i ∧ i<j+n ∧ p=(d,f i) := by
  induction n generalizing j with
  | zero => simp only [gridProfile,List.not_mem_nil] at hp
  | succ n ih =>
    simp only [gridProfile,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨j,le_rfl,by omega,rfl⟩
    · obtain ⟨i,hi,hij,rfl⟩ := ih hp
      exact ⟨i,by omega,by omega,rfl⟩

lemma gridProfile_pairwise {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hm : ∀ i k, j ≤ i → i<k → k<j+n → f i ≤ f k) :
    (gridProfile d f j n).Pairwise (fun p q ↦ p.2 ≤ q.2) := by
  induction n generalizing j with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [gridProfile,List.pairwise_cons]
    constructor
    · intro q hq
      obtain ⟨i,hi,hij,rfl⟩ := gridProfile_mem hq
      exact hm j i le_rfl (by omega) (by omega)
    · exact ih (fun i k hi hik hk ↦ hm i k (by omega) hik (by omega))

lemma gridProfile_sample {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hn : 0<n) {t : ℝ} (ht : t∈Icc (0 : ℝ) ((n : ℝ)*d)) :
    ∃ i, j ≤ i ∧ i<j+n ∧
      profileCoeff (gridProfile d f j n) t=(f i : ℝ) ∧
      0 ≤ (j : ℝ)*d+t-(i : ℝ)*d ∧ (j : ℝ)*d+t-(i : ℝ)*d ≤ d := by
  induction n generalizing j t with
  | zero => omega
  | succ n ih =>
    by_cases htd : t ≤ (d : ℝ)
    · refine ⟨j,le_rfl,by omega,?_,?_,?_⟩
      · exact patchTime_left _ _ htd
      · linarith [ht.1]
      · linarith
    · have hd : (d : ℝ)<t := lt_of_not_ge htd
      have hn' : 0<n := by
        by_contra hh
        have hn0 : n=0 := by omega
        subst n
        simp only [Nat.cast_one,zero_add,one_mul] at ht
        exact htd ht.2
      have ht' : t-(d : ℝ)∈Icc (0 : ℝ) ((n : ℝ)*d) := by
        constructor
        · linarith
        · have hu := ht.2
          rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul] at hu
          linarith
      obtain ⟨i,hij,hin,hc,hlo,hhi⟩ := ih hn' ht' (j := j+1)
      refine ⟨i,by omega,by omega,?_,?_,?_⟩
      · change patchTime (d : ℝ) _ _ t=_
        rw [patchTime_right _ _ hd]
        exact hc
      · simp only [Nat.cast_add,Nat.cast_one] at hlo
        nlinarith
      · simp only [Nat.cast_add,Nat.cast_one] at hhi
        nlinarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatTimeBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.restrict {T S : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hST : S ≤ T) : SmoothEvolution S γ V := by
  have hs : Icc (0 : ℝ) S⊆Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hST
  refine ⟨fun t ht ↦ h.slices t (hs ht),fun x ↦ (h.continuous_value x).mono hs,
    fun n x ↦ (h.continuous_jet n x).mono hs,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,fun t ht ↦ hb t (hs ht)⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := h.temporal n
    exact ⟨L,hL,fun s hs' t ht ↦ hb s (hs hs') t (hs ht)⟩
  · exact fun t ht s hs' ↦ h.value_pde t (hs ht) s (hs hs')
  · exact fun t ht s hs' ↦ h.gradient_pde t (hs ht) s (hs hs')

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ProfileSplit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma profileTime_append (l r:HeatProfile) : profileTime (l++r)=profileTime l+profileTime r := by
  induction l with
  | nil => simp [profileTime]
  | cons p l ih => simp only [List.cons_append,profileTime,ih,add_assoc]
lemma profileValue_append_zero (A:ℝ → ℝ) (l r:HeatProfile) :
    profileValue A (l++r) 0=profileValue (profileValue A r 0) l 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,profileValue_zero_cons,ih]
lemma profileValue_append_before (A:ℝ → ℝ) (l r:HeatProfile) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (profileTime l)) :
    profileValue A (l++r) t=profileValue (profileValue A r 0) l t := by
  induction l generalizing t with
  | nil => have ht0:t=0 := le_antisymm ht.2 ht.1; subst t; rfl
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
      congr 1
      exact profileValue_append_zero A l r
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact (sub_pos.mpr (lt_of_not_ge hp)).le
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith
lemma profileCoeff_append_before (l r:HeatProfile) {t:ℝ}
    (ht:t∈Ioc (0:ℝ) (profileTime l)) : profileCoeff (l++r) t=profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact sub_pos.mpr (lt_of_not_ge hp)
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma profileCoeff_append_after (l r:HeatProfile) {s:ℝ} (hs:profileTime l < s) :
    profileCoeff (l++r) s=profileCoeff r (s-profileTime l) := by
  induction l generalizing s with
  | nil => simp only [List.nil_append,profileTime,sub_zero]
  | cons p l ih =>
    have hp:(p.1:ℝ) < s := (le_add_of_nonneg_right (profileTime_nonneg l)).trans_lt hs
    change patchTime (p.1:ℝ) _ _ s=_
    rw [patchTime_right _ _ hp]
    have he:profileTime l < s-(p.1:ℝ) := by change (p.1:ℝ)+profileTime l < s at hs;linarith
    change profileCoeff (l++r) (s-(p.1:ℝ))=profileCoeff r (s-profileTime (p::l))
    rw [ih he]
    congr 1
    change s-(p.1:ℝ)-profileTime l=s-((p.1:ℝ)+profileTime l)
    ring

lemma splitLength_mul (a b:ℝ) (hab:a≤b) (n:ℕ) :
    ((n+1:ℕ):ℝ)*(splitLength a b hab n)=b-a := by
  change ((n+1:ℕ):ℝ)*((b-a)/(n+1:ℝ))=b-a
  rw [Nat.cast_add,Nat.cast_one]
  field_simp
lemma OrderParameter.splitSegment_time (γ:OrderParameter) (a b:ℝ) (hab:a≤b) (n:ℕ) :
    profileTime (γ.splitSegment a b hab n)=b-a := by
  rw [OrderParameter.splitSegment,gridProfile_time,splitLength_mul]
lemma split_sample_mem {a b:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1) {n i:ℕ} (hi:i<n+1) :
    a+(i:ℝ)*(splitLength a b hab.le n)∈Ico (0:ℝ) 1 := by
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast hi
  have ht:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at ht
  exact ⟨add_nonneg ha (mul_nonneg (Nat.cast_nonneg _) hd.le),by linarith⟩
lemma OrderParameter.splitSegment_mono (γ:OrderParameter) {a b:ℝ}
    (ha:0≤a) (hab:a<b) (hb:b≤1) (n:ℕ) :
    (γ.splitSegment a b hab.le n).Pairwise (fun p q ↦ p.2≤q.2) := by
  apply gridProfile_pairwise
  intro i k _ hik hk
  apply add_le_add _ le_rfl
  apply Real.toNNReal_mono
  exact γ.monotone (split_sample_mem ha hab hb (by omega))
    (split_sample_mem ha hab hb (by omega))
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hik.le) (splitLength a b hab.le n).coe_nonneg))
lemma OrderParameter.splitSegment_sample (γ:OrderParameter) {a b s:ℝ}
    (ha:0≤a) (hab:a<b) (hb:b≤1) (n:ℕ) (hs:s∈Icc (0:ℝ) (b-a)) :
    ∃ r∈Ico (0:ℝ) 1, a ≤ r ∧ r<b ∧
      profileCoeff (γ.splitSegment a b hab.le n) s=γ.coeff r+(gridDelta n:ℝ) ∧
      r≤a+s ∧ a+s-r≤(splitLength a b hab.le n:ℝ) := by
  obtain ⟨i,hi,hin,hc,hlo,hhi⟩:=gridProfile_sample (d:=splitLength a b hab.le n)
    (f:=fun i ↦ (γ.coeff (a+(i:ℝ)*(splitLength a b hab.le n))).toNNReal+gridDelta n)
    (j:=0) (Nat.succ_pos n) (by simpa only [splitLength_mul] using hs)
  have hr:=split_sample_mem ha hab hb (show i<n+1 by omega)
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast (show i<n+1 by omega)
  have ht:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at ht
  refine ⟨a+(i:ℝ)*(splitLength a b hab.le n),hr,le_add_of_nonneg_right (by positivity),by linarith,?_,?_,?_⟩
  · simpa only [OrderParameter.splitSegment,NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ hr)] using hc
  · simp only [Nat.cast_zero,zero_mul,zero_add] at hlo;linarith
  · simp only [Nat.cast_zero,zero_mul,zero_add] at hhi;linarith

lemma OrderParameter.splitGrid_time (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    profileTime (γ.splitGrid t n)=1 := by
  rw [OrderParameter.splitGrid,profileTime_append,γ.splitSegment_time,γ.splitSegment_time]
  ring
lemma OrderParameter.splitGrid_mono (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    (γ.splitGrid t n).Pairwise (fun p q ↦ p.2≤q.2) := by
  rw [OrderParameter.splitGrid,List.pairwise_append]
  refine ⟨γ.splitSegment_mono le_rfl t.property.1 t.property.2.le n,
    γ.splitSegment_mono t.property.1.le t.property.2 le_rfl n,?_⟩
  intro p hp q hq
  obtain ⟨i,_,hi,rfl⟩:=gridProfile_mem hp
  obtain ⟨j,_,hj,rfl⟩:=gridProfile_mem hq
  apply add_le_add _ le_rfl
  apply Real.toNNReal_mono
  have hir:=split_sample_mem (a:=0) le_rfl t.property.1 t.property.2.le (show i<n+1 by omega)
  have hjr:=split_sample_mem t.property.1.le t.property.2 le_rfl (show j<n+1 by omega)
  apply γ.monotone hir hjr
  have hi':(i:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show i≤n+1 by omega)
  have hle:=mul_le_mul_of_nonneg_right hi' (splitLength 0 t t.property.1.le n).coe_nonneg
  rw [splitLength_mul] at hle
  have hj0:0≤(j:ℝ)*(splitLength t 1 t.property.2.le n) := by positivity
  linarith
lemma OrderParameter.splitGrid_sample (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    ∃ r∈Ico (0:ℝ) 1,profileCoeff (γ.splitGrid t n) s=γ.coeff r+(gridDelta n:ℝ) ∧
      r ≤ s ∧ s-r ≤ (gridDelta n:ℝ) := by
  have hd:0<(n+1:ℝ) := by positivity
  by_cases hst:s≤t
  · have he:profileCoeff (γ.splitGrid t n) s=profileCoeff (γ.splitSegment 0 t t.property.1.le n) s := by
      rcases hs.1.eq_or_lt with rfl | hs0
      · change patchTime _ _ _ 0=patchTime _ _ _ 0
        rw [patchTime_left _ _ (splitLength 0 t t.property.1.le n).coe_nonneg,
          patchTime_left _ _ (splitLength 0 t t.property.1.le n).coe_nonneg]
      · exact profileCoeff_append_before _ _ ⟨hs0,by simpa only [γ.splitSegment_time,sub_zero] using hst⟩
    obtain ⟨r,hr,_,_,hc,hrs,hclose⟩:=γ.splitSegment_sample le_rfl t.property.1 t.property.2.le n
      (show s∈Icc (0:ℝ) ((t:ℝ)-0) by exact ⟨hs.1,by simpa only [sub_zero] using hst⟩)
    refine ⟨r,hr,he.trans hc,by simpa only [zero_add] using hrs,?_⟩
    have hlen:(splitLength 0 t t.property.1.le n:ℝ)≤gridDelta n :=
      div_le_div_of_nonneg_right (by simpa only [sub_zero] using t.property.2.le) hd.le
    simpa only [zero_add] using hclose.trans hlen
  · have ht:(t:ℝ) < s := lt_of_not_ge hst
    have he:profileCoeff (γ.splitGrid t n) s=profileCoeff (γ.splitSegment t 1 t.property.2.le n) (s-t) := by
      rw [OrderParameter.splitGrid,profileCoeff_append_after _ _ (by rw [γ.splitSegment_time,sub_zero];exact ht),γ.splitSegment_time,sub_zero]
    obtain ⟨r,hr,_,_,hc,hrs,hclose⟩:=γ.splitSegment_sample t.property.1.le t.property.2 le_rfl n
      (show s-(t:ℝ)∈Icc (0:ℝ) (1-t) by constructor <;> linarith [hs.2])
    refine ⟨r,hr,he.trans hc,?_,?_⟩
    · linarith
    · have hlen:(splitLength t 1 t.property.2.le n:ℝ)≤gridDelta n :=
        div_le_div_of_nonneg_right (by linarith [t.property.1]) hd.le
      linarith
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitConvergence
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma gridDelta_le_one (n:ℕ) : (gridDelta n:ℝ)≤1 := by
  change 1/(n+1:ℝ)≤1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]
lemma OrderParameter.splitGrid_le (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) :
    profileCoeff (γ.splitGrid t n) s≤γ.coeff s+(gridDelta n:ℝ) := by
  obtain ⟨r,hr,he,hrs,_⟩:=γ.splitGrid_sample t n ⟨hs.1,hs.2.le⟩
  rw [he]
  exact add_le_add (γ.monotone hr hs hrs) le_rfl
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
lemma profileHeight_nonneg (l:HeatProfile) : 0 ≤ profileHeight l := by
  cases l with
  | nil => exact le_rfl
  | cons p l => exact p.2.coe_nonneg.trans (le_max_left _ _)
lemma splitSmoothParameter_pos (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    0 < splitSmoothParameter γ t n := add_pos_of_pos_of_nonneg (by positivity) (profileHeight_nonneg _)
lemma splitSmooth_evolution (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothEvolution 1 (profileCoeff (γ.splitGrid t n)) (splitSmooth γ t n) := by
  unfold splitSmooth
  convert (logCoshTerminal_smoothTerminal (splitSmoothParameter_pos γ t n)).profile_evolution (γ.splitGrid t n) using 1
  all_goals try with_reducible_and_instances rfl
  exact (γ.splitGrid_time t n).symm
lemma splitSmooth_bulk_jets (γ:OrderParameter) (t:Ioo (0:ℝ) 1) {S:ℝ}
    (hS:S∈Ico (0:ℝ) 1) (m:ℕ) :
    ∃ C:ℝ,0 ≤ C ∧ ∀ n s,s∈Icc (0:ℝ) S → ∀ k ≤ m,∀ x,
      |iteratedDeriv k (deriv (splitSmooth γ t n s)) x| ≤ C := by
  let T:=(S+1)/2
  have hST:S<T := by dsimp only [T];linarith [hS.2]
  have hT1:T<1 := by dsimp only [T];linarith [hS.2]
  have hT:T∈Ico (0:ℝ) 1 := ⟨hS.1.trans hST.le,hT1⟩
  obtain ⟨C,hC,hb⟩:=uniform_bulk_jets (γ.coeff T+1) (by linarith [γ.nonneg _ hT]) T m S hS.1 hST
  refine ⟨C,hC,?_⟩
  intro n s hs k hk x
  exact hb (profileCoeff (γ.splitGrid t n)) (splitSmooth γ t n)
    ((splitSmooth_evolution γ t n).restrict hT1.le) (profileCoeff_measurable _)
    ((profileCoeff_mono (γ.splitGrid_mono t n)).mono (by rw [γ.splitGrid_time];exact Icc_subset_Icc le_rfl hT1.le))
    (fun r hr ↦ by
      rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
      exact (γ.splitGrid_le t n ⟨hr.1,hr.2.trans_lt hT1⟩).trans
        (add_le_add (γ.monotone ⟨hr.1,hr.2.trans_lt hT1⟩ hT hr.2) (gridDelta_le_one n))) s hs k hk x
lemma splitSmooth_jet_limits (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) {S:ℝ}
    (hS:S∈Ico (0:ℝ) 1) (k:ℕ) :
    TendstoUniformly (fun n (p:Icc (0:ℝ) S×ℝ) ↦ iteratedDeriv k (splitSmooth γ t n p.1) p.2)
      (fun p ↦ iteratedDeriv k (phi W γ p.1) p.2) atTop := by
  let f:Icc (0:ℝ) S×ℝ → Ico (0:ℝ) 1×ℝ := fun p ↦ (⟨p.1,⟨p.1.property.1,p.1.property.2.trans_lt hS.2⟩⟩,p.2)
  have hl:= (splitSmooth_tendsto W γ t).comp f
  have hs (n:ℕ) (s:Icc (0:ℝ) S):ContDiff ℝ ∞ (splitSmooth γ t n s) :=
    ((splitSmooth_evolution γ t n).slices s ⟨s.property.1,s.property.2.trans hS.2.le⟩).smooth
  have hb (j:ℕ):∃ C:ℝ,0 ≤ C ∧ ∀ (n:ℕ) (s:Icc (0:ℝ) S) x,|iteratedDeriv (j+1) (splitSmooth γ t n s) x| ≤ C := by
    obtain ⟨C,hC,hb⟩:=splitSmooth_bulk_jets γ t hS j
    refine ⟨C,hC,fun n s x ↦ ?_⟩
    simpa only [iteratedDeriv_succ'] using hb n s s.property j le_rfl x
  have hl' : TendstoUniformly (fun n (p:Icc (0:ℝ) S×ℝ) ↦ splitSmooth γ t n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := hl
  exact (uniform_all_derivative_limits (f:=fun (s:Icc (0:ℝ) S) x ↦ phi W γ s x) hl' hs hb).1 k
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitShape
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma splitTerminal_eq (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    splitTerminal γ t n=splitSmooth γ t n t := by
  unfold splitSmooth OrderParameter.splitGrid
  rw [profileValue_append_before _ _ _ ⟨t.property.1.le,by rw [γ.splitSegment_time,sub_zero]⟩]
  have he:profileTime (γ.splitSegment 0 t t.property.1.le n)=(t:ℝ) := by rw [γ.splitSegment_time,sub_zero]
  exact (by simpa only [he,splitTerminal] using
    (profileValue_terminal (splitTerminal γ t n) (γ.splitSegment 0 t t.property.1.le n)).symm)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma splitTerminal_jets_limit (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ iteratedDeriv k (deriv (splitTerminal γ t n)) x)
      (fun x ↦ iteratedDeriv k (deriv (phi W γ t)) x) := by
  have ht:(t:ℝ)∈Ico (0:ℝ) 1 := ⟨t.property.1.le,t.property.2⟩
  have hl:TendstoUniformly (fun n x ↦ iteratedDeriv k (deriv (splitTerminal γ t n)) x)
      (fun x ↦ iteratedDeriv k (deriv (phi W γ t)) x) atTop := by
    simpa only [iteratedDeriv_succ',splitTerminal_eq,Function.comp_def] using
      (splitSmooth_jet_limits W γ t ht (k+1)).comp (fun x:ℝ ↦ (⟨(t:ℝ),⟨t.property.1.le,le_rfl⟩⟩,x))
  obtain ⟨C,hC,hb⟩:=splitSmooth_bulk_jets γ t ht k
  have hbd:∀ n x,|iteratedDeriv k (deriv (splitTerminal γ t n)) x| ≤ C := by
    intro n x
    rw [splitTerminal_eq]
    exact hb n t ⟨t.property.1.le,le_rfl⟩ k le_rfl x
  exact ⟨hl,C,hC,hbd,fun x ↦ le_of_tendsto (hl.tendsto_at x).abs (Eventually.of_forall (fun n ↦ hbd n x))⟩
lemma split_spatialJet_limit_oai (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ spatialJet (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) k x)
      (spatialJet (γ.coeff t) (phi W γ t) k) := by
  have hc:BoundedUniformLimit (fun n (_:ℝ) ↦ γ.coeff t+(gridDelta n:ℝ)) (fun _ ↦ γ.coeff t) := by
    apply BoundedUniformLimit.seq
    · change Tendsto (fun n:ℕ ↦ γ.coeff t+1/(n+1:ℝ)) atTop (𝓝 (γ.coeff t))
      simpa only [add_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (γ.coeff t))
    · refine ⟨γ.coeff t+1,by linarith [γ.nonneg _ ⟨t.property.1.le,t.property.2⟩],fun n ↦ ?_⟩
      rw [abs_of_nonneg (add_nonneg (γ.nonneg _ ⟨t.property.1.le,t.property.2⟩) (gridDelta n).coe_nonneg)]
      exact add_le_add le_rfl (gridDelta_le_one n)
  exact hc.mul (splitTerminal_jets_limit W γ t k)
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.split_spatialJet_limit_oai := @OAI.SKValue.split_spatialJet_limit_oai
