-- Prove2me | solution 1 for OAI.MomentSchauder.smooth_of_regular_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:21:47.937735+00:00
-- url     : https://prove2.me/submissions/6531429e-8adc-4c3f-932e-db0ef419eff2

import Mathlib
import Definitions.Def_OAIW2LB000

section
-- module Solutions.OAIW2_LogBM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

open Set Filter
open scoped Topology NNReal

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

open scoped ENNReal

open scoped InnerProductSpace ContDiff Topology
open scoped ENNReal

open Set MeasureTheory Filter
open scoped ENNReal Topology

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace AESlice
section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_lines {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) (e : E) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂(volume : Measure ℝ), P (x+t • e) := by
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hNae : ∀ᵐ x ∂μ, x∉N := by
    rw [ae_iff]
    convert hN0 using 2; ext x; simp
  have hpre : MeasurableSet {p : E×ℝ | p.1+p.2 • e∉N} := by
    exact (hNm.preimage (show Measurable (fun p : E×ℝ => p.1+p.2 • e) by fun_prop)).compl
  have ht : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂μ, x+t • e∉N := by
    exact ae_of_all _ (fun t => (measurePreserving_add_right μ (t • e)).quasiMeasurePreserving.ae hNae)
  have hh := (ae_ae_comm hpre).mpr ht
  filter_upwards [hh] with x hx
  filter_upwards [hx] with t ht
  exact not_not.mp (fun hn => ht (hN hn))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma line_lipschitz (x e : E) : LipschitzWith ‖e‖₊ (fun t : ℝ => x+t • e) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← sub_smul,norm_smul,Real.norm_eq_abs]
  exact le_of_eq (mul_comm _ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma line_deriv (g : E → ℝ) {x e : E} {t : ℝ} (hg : DifferentiableAt ℝ g (x+t • e)) :
    HasDerivAt (fun s : ℝ => g (x+s • e)) ((fderiv ℝ g (x+t • e)) e) t := by
  simpa only [id_eq,one_smul,Function.comp_def] using hg.hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const e).const_add x)

lemma difference_le_ae {g : E → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {e : E} {M : ℝ}
    (ha : ∀ᵐ x ∂μ, x∈Ω → DifferentiableAt ℝ g x ∧ fderiv ℝ g x e≤M)
    {x : E} {a : ℝ} (ha0 : 0≤a) (hx : x∈Ω) (hxa : x+a • e∈Ω) :
    g (x+a • e)-g x≤M*a := by
  have hl := ae_lines μ ha e
  let U : Set E := Ω∩(fun y => y+a • e) ⁻¹' Ω
  have hU : IsOpen U := hΩ.inter (hΩ.preimage (by fun_prop))
  have hxU : x∈U := ⟨hx,hxa⟩
  have hgood : ∀ᵐ y ∂μ, y∈U → g (y+a • e)-g y≤M*a := by
    filter_upwards [hl] with y hy hyU
    have hs (t : ℝ) (ht : t∈Icc 0 a) : y+t • e∈Ω := by
      by_cases haZ : a=0
      · have htZ : t=0 := by rw [haZ] at ht; linarith [ht.1,ht.2]
        simpa only [htZ,zero_smul,add_zero] using hyU.1
      have haP : 0<a := lt_of_le_of_ne ha0 (Ne.symm haZ)
      have hh := hc hyU.1 hyU.2 (show 0≤1-t/a by rw [sub_nonneg]; exact (div_le_one haP).mpr ht.2)
        (div_nonneg ht.1 ha0) (by ring : (1-t/a)+t/a=1)
      convert hh using 1
      dsimp only at hh ⊢
      simp only [smul_add,smul_smul,sub_smul,one_smul]
      rw [div_mul_cancel₀ _ haZ]
      abel
    have hline := hg.comp (line_lipschitz y e)
    have hac : AbsolutelyContinuousOnInterval (fun s => g (y+s • e)) 0 a :=
      hline.lipschitzOnWith.absolutelyContinuousOnInterval
    have hi := hac.intervalIntegrable_deriv
    have hd : ∀ᵐ t ∂(volume.restrict (Icc 0 a)), deriv (fun s => g (y+s • e)) t≤M := by
      filter_upwards [ae_restrict_of_ae hy,ae_restrict_mem measurableSet_Icc] with t ht hta
      rw [(line_deriv g (ht (hs t hta)).1).deriv]
      exact (ht (hs t hta)).2
    have hh := intervalIntegral.integral_mono_ae_restrict ha0 hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 a) hd
    rw [hac.integral_deriv_eq_sub] at hh
    simpa only [zero_smul,add_zero,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using hh
  have hdense := μ.dense_of_ae hgood
  have hcl := hdense.open_subset_closure_inter hU hxU
  have hclosed : IsClosed {y : E | g (y+a • e)-g y≤M*a} :=
    isClosed_le ((hg.continuous.comp (by fun_prop)).sub hg.continuous) continuous_const
  exact hclosed.closure_subset_iff.mpr (fun y hy => hy.2 hy.1) hcl

end
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal
open scoped InnerProductSpace


end AESlice

end

noncomputable section

namespace ContinuousEnvelope
open Filter Set Metric
open scoped Topology
variable {E : Type*} {F : Type*} [MetricSpace E] [MetricSpace F] [CompleteSpace F]

theorem exists_continuous_extension {G : Set E} (hG : Dense G) (H : E → F)
    (hosc : ∀ c : E,∀ ε > 0,∃ δ > 0,∀ x∈G,dist x c<δ →
      ∀ y∈G,dist y c<δ → dist (H x) (H y)<ε) :
    ∃ A : E → F,Continuous A ∧ ∀ x∈G,A x=H x := by
  let h := hG.isDenseInducing_val
  let f : G → F := fun x => H x
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hb⟩ := hosc x ε hε
    refine ⟨δ,hδ,fun y hy => ?_⟩
    exact hb y y.prop hy x x.prop (by simpa only [dist_self] using hδ)
  have hc (c : E) : Cauchy (Filter.map f (Filter.comap Subtype.val (𝓝 c))) := by
    let := h.comap_nhds_neBot c
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance,?_⟩
    intro ε hε
    obtain ⟨δ,hδ,hb⟩ := hosc c ε hε
    let U : Set G := {x | dist (x:E) c<δ}
    refine ⟨f '' U,?_,?_⟩
    · rw [Filter.mem_map]
      apply Filter.mem_comap.mpr
      refine ⟨ball c δ,ball_mem_nhds c hδ,?_⟩
      intro x hx
      exact mem_preimage.mpr (mem_image_of_mem f hx)
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      exact hb x x.prop hx y y.prop hy
  exact ⟨h.extend f,h.continuous_extend_of_cauchy hc,fun x hx => h.extend_eq hf ⟨x,hx⟩⟩

end ContinuousEnvelope

end

namespace GridHolder
open Metric

lemma pow_rpow {q k a : ℝ} (hq : 0≤q) (he : q^a=k) (N : ℕ) :
    (q^N)^a=k^N := by
  rw [← Real.rpow_natCast_mul hq,mul_comm,Real.rpow_mul_natCast hq,he]

theorem of_grid {E : Type*} {F : Type*} [MetricSpace E] [MetricSpace F]
    {f : E → F} {q k a M R : ℝ} (hq : 0<q) (hq1 : q<1) (hk : 0<k)
    (ha : 0<a) (he : q^a=k) (hM : 0≤M) (hR : 0<R)
    (hb : ∀ N x y,dist x y≤R*q^N → dist (f x) (f y)≤M*k^N) :
    ∀ x y,dist x y≤R → dist (f x) (f y)≤(M/k)*(dist x y/R)^a := by
  intro x y hxy
  by_cases hd : dist x y=0
  · have heq := dist_eq_zero.mp hd
    subst y
    simp [Real.zero_rpow ha.ne']
  · have hd0 : 0<dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hd0 hR)
      ((div_le_one hR).mpr hxy) hq hq1
    have hg := hb N x y (by have hh := (div_le_iff₀ hR).mp hhi; simpa only [mul_comm] using hh)
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤q^(N+1)) hlo.le ha.le
    rw [pow_rpow hq.le he,pow_succ] at hp
    calc
      dist (f x) (f y) ≤ M*k^N := hg
      _ = (M/k)*(k^N*k) := by field_simp
      _ ≤ (M/k)*(dist x y/R)^a := mul_le_mul_of_nonneg_left hp (div_nonneg hM hk.le)
end GridHolder

end

section

open scoped Real

open MeasureTheory
open scoped Topology

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff

open Filter Function
open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff

open MeasureTheory
open scoped Topology ContDiff

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace MomentDifferential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_det : ContDiff ℝ ∞ (fun A : Matrix ι ι ℝ => A.det) :=
  (detMultilinear (ι := ι)).contDiff

lemma det_updateRow_eq (A : Matrix ι ι ℝ) (i : ι) (v : ι → ℝ) :
    (A.updateRow i v).det = ∑ j, A.adjugate j i * v j := by
  have h := congrFun (Matrix.cramer_eq_adjugate_mulVec Aᵀ v) i
  simpa only [Matrix.cramer_apply, Matrix.updateCol_transpose,
    Matrix.det_transpose, ← Matrix.adjugate_transpose, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply] using h

lemma det_linearDeriv (A B : Matrix ι ι ℝ) :
    detMultilinear.linearDeriv A B = (A.adjugate * B).trace := by
  change detMultilinear.linearDeriv (fun i j => A i j) (fun i j => B i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (B i)).det) = _
  simp_rw [det_updateRow_eq]
  rw [Finset.sum_comm]
  rfl

end MomentDifferential

end

open scoped ContDiff Topology

open Matrix
open scoped BigOperators Kronecker

open MeasureTheory
open scoped BigOperators

open scoped BigOperators InnerProductSpace Topology

end



noncomputable section
namespace SchwartzKernel
open Set MeasureTheory Filter Metric FourierTransform
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_eq_fourier_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : 𝓢(E,F)) : (∫ t,K t)=(𝓕 K) 0 := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq]
  simp

lemma integral_fourierInv (K : 𝓢(E,ℂ)) : (∫ t,(𝓕⁻ K) t)=K 0 := by
  rw [integral_eq_fourier_zero,FourierTransform.fourier_fourierInv_eq]

lemma integral_derivative (K : 𝓢(E,ℂ)) : ∫ t,fderiv ℝ K t=0 := by
  change (∫ t,(SchwartzMap.fderivCLM ℝ E ℂ K) t)=0
  rw [integral_eq_fourier_zero,SchwartzMap.fourier_fderivCLM_eq]
  ext v
  simp [SchwartzMap.smulRightCLM_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_bound (K : 𝓢(E,ℂ)) : ∃ D,0≤D ∧ ∀ x,‖fderiv ℝ K x‖≤D := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ E ℂ K),by positivity,?_⟩
  exact fun x => (SchwartzMap.fderivCLM ℝ E ℂ K).norm_le_seminorm ℝ x

theorem hasFDerivAt_convolution (K : 𝓢(E,ℂ)) {f : E → ℂ}
    (hf : Integrable f volume) (x : E) :
    HasFDerivAt (fun x => ∫ t,f t*K (x-t))
      (∫ t,f t • fderiv ℝ K (x-t)) x := by
  obtain ⟨D,_hD,hDb⟩ := derivative_bound K
  have hi (y : E) : Integrable (fun t => f t*K (y-t)) volume := by
    refine (hf.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 K)).mono' ?_ ?_
    · exact hf.aestronglyMeasurable.mul ((K.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (K.norm_le_seminorm ℝ _) (norm_nonneg _)
  have hder (t y : E) : HasFDerivAt (fun y => f t*K (y-t)) (f t • fderiv ℝ K (y-t)) y := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,Pi.smul_apply,smul_eq_mul] using
      (((K.differentiable (y-t)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const t)).const_mul (f t))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun y t => f t • fderiv ℝ K (y-t)) (bound := fun t => ‖f t‖*D) (s:=univ) (by simp) ?_ (hi x) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun y => (hi y).aestronglyMeasurable)
  · exact hf.aestronglyMeasurable.smul (((K.smooth 1).continuous_fderiv one_ne_zero).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with t
    intro y _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hDb _) (norm_nonneg _)
  · exact hf.norm.mul_const D
  · filter_upwards with t
    intro y _
    exact hder t y

end SchwartzKernel
namespace ScaledKernel
open MeasureTheory Set Filter Metric
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma change_variables (f : E → F) {r : ℝ} (hr : 0<r) (x : E) :
    (∫ t,f t)=(r^Module.finrank ℝ E) • ∫ t,f (x-r • t) := by
  have he := Measure.integral_comp_smul_of_nonneg (volume:Measure E) (fun t => f (x-t)) r (hR:=hr.le)
  rw [integral_sub_left_eq_self] at he
  rw [he,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),one_smul]

omit [MeasurableSpace E] [BorelSpace E] in
lemma dilate_fderiv (K : 𝓢(E,ℂ)) (r : ℝ) (hr : r≠0) (x : E) :
    fderiv ℝ (dilate K r hr) x=r • fderiv ℝ K (r • x) := by
  have hh := (K.differentiable (r • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  change HasFDerivAt (fun y : E => K (r • y)) _ x at hh
  change fderiv ℝ (fun y : E => K (r • y)) x = _
  rw [hh.fderiv]
  ext v
  simp

lemma apply_eq (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) (f : E → ℂ) (x : E) :
    applyKernel K r f x=(r^Module.finrank ℝ E)⁻¹ • ∫ t,f t*K (r⁻¹ • (x-t)) := by
  rw [change_variables (fun t => f t*K (r⁻¹ • (x-t))) hr x,smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hr.ne'),one_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [show x-(x-r • t)=r • t by abel,inv_smul_smul₀ hr.ne']
  exact mul_comm _ _

lemma derivative (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) {f : E → ℂ}
    (hf : Integrable f volume) (x : E) :
    HasFDerivAt (applyKernel K r f)
      (r⁻¹ • ∫ t,f (x-r • t) • fderiv ℝ K t) x := by
  let K' := dilate K r⁻¹ (inv_ne_zero hr.ne')
  have hh := (SchwartzKernel.hasFDerivAt_convolution K' hf x).const_smul (r^Module.finrank ℝ E)⁻¹
  have hfun : (applyKernel K r f)=(fun x => (r^Module.finrank ℝ E)⁻¹ • ∫ t,f t*K' (x-t)) :=
    funext (apply_eq K hr f)
  change HasFDerivAt (fun z => (r^Module.finrank ℝ E)⁻¹ • ∫ t,f t*K' (z-t))
    ((r^Module.finrank ℝ E)⁻¹ • ∫ t,f t • fderiv ℝ K' (x-t)) x at hh
  rw [← hfun] at hh
  have he : (r^Module.finrank ℝ E)⁻¹ • (∫ t,f t • fderiv ℝ K' (x-t)) =
      r⁻¹ • ∫ t,f (x-r • t) • fderiv ℝ K t := by
    simp_rw [K',dilate_fderiv,smul_comm (f _) r⁻¹]
    rw [integral_smul,change_variables (fun t => f t • fderiv ℝ K (r⁻¹ • (x-t))) hr x]
    simp_rw [show ∀ t:E,x-(x-r • t)=r • t by intro t; abel,inv_smul_smul₀ hr.ne']
    rw [smul_smul,smul_smul]
    congr 1
    field_simp
  rw [he] at hh
  exact hh

end ScaledKernel

namespace AnnularSymbol
open Set Filter Metric FourierTransform
open scoped SchwartzMap Topology InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma symbol_zero (A : E →L[ℝ] E) (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) :
    symbol A hA v w 0=0 := by
  simp [symbol,multiplier]

end AnnularSymbol

namespace AnnularFourier
section
open Set MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fourier_conv (f g : 𝓢(E,ℂ)) : 𝓕 (conv f g)=product (𝓕 f) (𝓕 g) :=
  SchwartzMap.fourier_convolution _ _ _

lemma fourier_dilate (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) (x : E) :
    𝓕 (ScaledKernel.dilate K r hr.ne') x=
      (r^Module.finrank ℝ E)⁻¹ • 𝓕 K (r⁻¹ • x) := by
  rw [SchwartzMap.fourier_coe,SchwartzMap.fourier_coe,Real.fourier_eq,Real.fourier_eq]
  have hh := Measure.integral_comp_smul_of_nonneg (volume:Measure E)
    (fun t => Real.fourierChar (-⟪t,r⁻¹ • x⟫_ℝ) • K t) r (hR:=hr.le)
  convert hh using 1
  apply integral_congr_ae
  filter_upwards with t
  rw [real_inner_smul_left,real_inner_smul_right,mul_inv_cancel_left₀ hr.ne']
  rfl

lemma fourier_second (u : 𝓢(E,ℂ)) (v w x : E) :
    𝓕 (∂_{v} (∂_{w} u)) x=
      (2*Real.pi*Complex.I)^2*(Complex.ofReal ⟪x,v⟫_ℝ *Complex.ofReal ⟪x,w⟫_ℝ)*𝓕 u x := by
  have hv : (fun x:E => inner ℝ x v).HasTemperateGrowth := by fun_prop
  have hw : (fun x:E => inner ℝ x w).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq,SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply,SchwartzMap.smulLeftCLM_apply_apply hv,
    SchwartzMap.smulLeftCLM_apply_apply hw,smul_eq_mul,Complex.real_smul]
  ring

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma quadratic_sum (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (x : E) :
    ∑ i,⟪x,b i⟫_ℝ *⟪x,A (b i)⟫_ℝ =⟪x,A x⟫_ℝ := by
  calc
    _ = ⟪x,A (∑ i,(b.repr x) i • b i)⟫_ℝ := by
      simp only [map_sum,map_smul,inner_sum,real_inner_smul_right,OrthonormalBasis.repr_apply_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm (b i) x]
    _ = _ := by rw [b.sum_repr]

lemma fourier_elliptic (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (u : 𝓢(E,ℂ)) (x : E) :
    𝓕 (elliptic b A u) x=(2*Real.pi*Complex.I)^2*Complex.ofReal ⟪x,A x⟫_ℝ *𝓕 u x := by
  simp only [elliptic,FourierTransform.fourier_sum,sum_apply,fourier_second]
  rw [← Finset.sum_mul,← Finset.mul_sum]
  simp_rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum,quadratic_sum]
end
section
open Set MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fourier_normalized (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) (x : E) :
    𝓕 (normalized K r hr.ne') x=𝓕 K (r • x) := by
  rw [normalized,fourier_smul,smul_apply,fourier_dilate K (inv_pos.mpr hr),inv_inv,
    inv_pow,inv_inv,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ hr.ne'),one_smul]

lemma normalized_conv (K u : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) (x : E) :
    conv (normalized K r hr.ne') u x=ScaledKernel.applyKernel K r u x := by
  rw [conv,SchwartzMap.convolution_apply,convolution_def]
  simp only [ContinuousLinearMap.mul_apply',normalized,smul_apply,ScaledKernel.dilate_apply,smul_mul_assoc]
  rw [integral_smul]
  have hh := Measure.integral_comp_smul_of_nonneg (volume:Measure E)
    (fun t => K (r⁻¹ • t)*u (x-t)) r (hR:=hr.le)
  rw [← hh]
  simp only [inv_smul_smul₀ hr.ne',ScaledKernel.applyKernel]

omit [MeasurableSpace E] [BorelSpace E] in
lemma inverse_scaled (A : E →L[ℝ] E) (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w x : E)
    {r : ℝ} (hr : r≠0) :
    AnnularSymbol.symbol A hA v w (r • x)*Complex.ofReal ⟪x,A x⟫_ℝ =
      Complex.ofReal (AnnularSymbol.cutoff (r • x)*⟪x,v⟫_ℝ *⟪x,w⟫_ℝ) := by
  by_cases hx : x=0
  · subst x; simp [AnnularSymbol.symbol,AnnularSymbol.multiplier]
  · change Complex.ofReal (AnnularSymbol.cutoff (r • x)*
      (⟪r • x,v⟫_ℝ *⟪r • x,w⟫_ℝ /⟪r • x,A (r • x)⟫_ℝ))*_= _
    rw [← Complex.ofReal_mul]
    congr 1
    simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
    field_simp [(hA x hx).ne',hr]

variable {ι : Type*} [Fintype ι]

theorem annular_identity (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) (u : 𝓢(E,ℂ))
    {r : ℝ} (hr : 0<r) :
    conv (normalized (AnnularSymbol.kernel A hA v w) r hr.ne') (elliptic b A u)=
      𝓕⁻ (product (ScaledKernel.dilate annulus r hr.ne') (𝓕 (∂_{v} (∂_{w} u)))) := by
  have he : 𝓕 (conv (normalized (AnnularSymbol.kernel A hA v w) r hr.ne') (elliptic b A u))=
      product (ScaledKernel.dilate annulus r hr.ne') (𝓕 (∂_{v} (∂_{w} u))) := by
    ext x
    rw [fourier_conv,product_apply,fourier_normalized _ hr,AnnularSymbol.kernel,
      FourierTransform.fourier_fourierInv_eq,fourier_elliptic,product_apply,ScaledKernel.dilate_apply,
      annulus_apply,fourier_second]
    have hi := inverse_scaled A hA v w x hr.ne'
    simp only [Complex.ofReal_mul] at hi
    calc
      _ = (2*Real.pi*Complex.I)^2*(AnnularSymbol.symbol A hA v w (r • x)*
          Complex.ofReal ⟪x,A x⟫_ℝ)*𝓕 u x := by ring
      _ = _ := by rw [hi]; ring
  rw [← he,FourierTransform.fourierInv_fourier_eq]
end
open Set MeasureTheory FourierTransform Filter LineDeriv
open scoped SchwartzMap InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma lowSymbol_zero : (lowSymbol : 𝓢(E,ℂ)) 0=1 := by
  rw [lowSymbol_apply,(lowBump (E:=E)).one_of_mem_closedBall (by simp [lowBump])]
  rfl
omit [MeasurableSpace E] [BorelSpace E] in
lemma lowSymbol_bound (x : E) : ‖(lowSymbol : 𝓢(E,ℂ)) x‖≤1 := by
  rw [lowSymbol_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ((lowBump (E:=E)).nonneg)]
  exact (lowBump (E:=E)).le_one

omit [MeasurableSpace E] [BorelSpace E] in
lemma annulus_low (x : E) : (annulus : 𝓢(E,ℂ)) x=lowSymbol ((1/2:ℝ) • x)-lowSymbol x := by
  change Complex.ofReal (_-_)=Complex.ofReal _-Complex.ofReal _
  rw [Complex.ofReal_sub]
  rfl

lemma lowFilter_tendsto (u : 𝓢(E,ℂ)) {r : ℕ → ℝ} (hr : ∀ n,r n≠0)
    (hlim : Tendsto r atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => lowFilter u (r n) (hr n) x) atTop (𝓝 (u x)) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := (volume : Measure E))
    (F := fun (n:ℕ) (t:E) => Real.fourierChar ⟪t,x⟫_ℝ • ((lowSymbol : 𝓢(E,ℂ)) (r n • t)*𝓕 u t))
    (f := fun t:E => Real.fourierChar ⟪t,x⟫_ℝ • 𝓕 u t)
    (fun t:E => ‖𝓕 u t‖)
    (fun n => ((Real.continuous_fourierChar.comp (by fun_prop : Continuous (fun t:E => ⟪t,x⟫_ℝ))).smul
      (((lowSymbol : 𝓢(E,ℂ)).continuous.comp (continuous_const.smul continuous_id : Continuous (fun t:E => r n • t))).mul (𝓕 u).continuous)).aestronglyMeasurable)
    (𝓕 u).integrable.norm
    (fun n => Filter.Eventually.of_forall (fun t => by
      rw [Circle.norm_smul,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (lowSymbol_bound _)))
    (Filter.Eventually.of_forall (fun t:E => by
      have hrt : Tendsto (fun n => r n • t) atTop (𝓝 (0:E)) := by simpa using hlim.smul_const t
      have hchi := ((lowSymbol : 𝓢(E,ℂ)).continuous.tendsto 0).comp hrt
      rw [lowSymbol_zero] at hchi
      simpa only [one_mul,Function.comp_def] using (tendsto_const_nhds.smul (hchi.mul_const (𝓕 u t)))))
  have hu : (∫ t:E,Real.fourierChar ⟪t,x⟫_ℝ • 𝓕 u t)=u x := by
    rw [← Real.fourierInv_eq,← SchwartzMap.fourierInv_coe,FourierTransform.fourierInv_fourier_eq]
  rw [hu] at hh
  simpa only [lowFilter,SchwartzMap.fourierInv_coe,Real.fourierInv_eq,product_apply,
    ScaledKernel.dilate_apply] using hh

lemma inverse_sub (f g : 𝓢(E,ℂ)) : 𝓕⁻ (f-g)=𝓕⁻ f-𝓕⁻ g :=
  map_sub (fourierInvCLM ℂ (𝓢(E,ℂ))) f g

lemma piece_telescope (u : 𝓢(E,ℂ)) (n : ℕ) :
    𝓕⁻ (product (ScaledKernel.dilate annulus ((1/2:ℝ)^n) (pow_ne_zero _ (by norm_num))) (𝓕 u))=
      lowFilter u ((1/2:ℝ)^(n+1)) (pow_ne_zero _ (by norm_num))-
      lowFilter u ((1/2:ℝ)^n) (pow_ne_zero _ (by norm_num)) := by
  rw [lowFilter,lowFilter,← inverse_sub]
  congr 1
  ext x
  simp only [product_apply,ScaledKernel.dilate_apply,sub_apply,annulus_low,pow_succ]
  simp only [smul_smul]
  rw [mul_comm ((1/2:ℝ)^n) (1/2)]
  ring
end AnnularFourier
namespace VectorKernelHolder
open MeasureTheory Set Filter Metric
open scoped SchwartzMap NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rpow_bound {a : ℝ} (ha : 0≤a) (ha1 : a≤1) (t : ℝ) (ht : 0≤t) :
    t^a≤1+t := by
  by_cases ht1 : t≤1
  · exact (Real.rpow_le_one ht ht1 ha).trans (le_add_of_nonneg_right ht)
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge ht1)) ha1
    rw [Real.rpow_one] at hh
    linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma integrable_moment (K : 𝓢(E,F)) {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    Integrable (fun t => ‖K t‖*‖t‖^a) volume := by
  have hi := K.integrable.norm.add (K.integrable_pow_mul volume 1)
  apply hi.mono' ((K.continuous.norm.mul (continuous_norm.rpow_const (fun _ => Or.inr ha.le))).aestronglyMeasurable)
  filter_upwards with t
  change ‖‖K t‖*‖t‖^a‖ ≤ ‖K t‖+‖t‖^1*‖K t‖
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  simpa only [pow_one,mul_add,mul_one,mul_comm,add_mul,one_mul] using
    mul_le_mul_of_nonneg_left (rpow_bound ha.le ha1 ‖t‖ (norm_nonneg _)) (norm_nonneg (K t))

omit [CompleteSpace F] in

theorem cancellation_bound (K : 𝓢(E,F)) (hK : ∫ t,K t=0)
    {a C r : ℝ} (ha : 0<a) (ha1 : a≤1) (_hC : 0≤C) (hr : 0<r)
    {f : E → ℂ} (hf : Continuous f)
    (hB : ∃ B,∀ x,‖f x‖≤B)
    (hhold : ∀ x y,dist (f x) (f y)≤C*dist x y^a) (x : E) :
    ‖∫ t,f (x-r • t) • K t‖≤C*r^a*(∫ t,‖K t‖*‖t‖^a) := by
  obtain ⟨B,hB⟩ := hB
  have hi : Integrable (fun t => f (x-r • t) • K t) volume := by
    apply (K.integrable.norm.mul_const B).mono' (((hf.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul K.continuous).aestronglyMeasurable)
    filter_upwards with t
    change ‖f (x-r • t) • K t‖≤‖K t‖*B
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hic : Integrable (fun t => f x • K t) volume := K.integrable.smul _
  have he : (∫ t,f (x-r • t) • K t)=∫ t,(f (x-r • t)-f x) • K t := by
    simp_rw [sub_smul]
    rw [integral_sub hi hic,integral_smul,hK,smul_zero,sub_zero]
  rw [he]
  have hm := integrable_moment K ha ha1
  calc
    _ ≤ ∫ t,‖(f (x-r • t)-f x) • K t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t,C*r^a*(‖K t‖*‖t‖^a) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hm.const_mul _)
      filter_upwards with t
      rw [norm_smul]
      have hh := hhold (x-r • t) x
      simp only [dist_eq_norm] at hh
      rw [show x-r • t-x = -(r • t) by abel,norm_neg,norm_smul,
        Real.norm_eq_abs,abs_of_pos hr,Real.mul_rpow hr.le (norm_nonneg _)] at hh
      nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg (K t))]
    _ = _ := integral_const_mul _ _

end VectorKernelHolder

namespace ScaleSeries
open Set Filter Metric
open scoped NNReal Topology
variable {E : Type*} {F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] [CompleteSpace F]

lemma summable_bound {k C : ℝ} (hk0 : 0≤k) (hk : k<1) {f : ℕ → F}
    (hb : ∀ n,‖f n‖≤C*k^n) : Summable f := by
  have hs : Summable (fun n : ℕ => k^n) := summable_geometric_of_norm_lt_one
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg hk0] using hk)
  exact Summable.of_norm_bounded (hs.mul_left C) hb

omit [CompleteSpace F] in
lemma tail_bound {k C : ℝ} (hk0 : 0≤k) (hk : k<1) {f : ℕ → F}
    (hb : ∀ n,‖f n‖≤C*k^n) (N : ℕ) : ‖∑' n,f (n+N)‖≤C*k^N/(1-k) := by
  have hgeo : Summable (fun n : ℕ => k^n) := summable_geometric_of_norm_lt_one
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg hk0] using hk)
  have hg : Summable (fun n => C*k^(n+N)) := by
    simpa only [pow_add,mul_left_comm,mul_assoc,mul_comm] using hgeo.mul_left (C*k^N)
  have hnorm : Summable (fun n => ‖f (n+N)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hb (n+N)) hg
  calc
    _ ≤ ∑' n, ‖f (n+N)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, C*k^(n+N) := Summable.tsum_le_tsum (fun n => hb (n+N)) hnorm hg
    _ = C*k^N/(1-k) := by
      simp_rw [pow_add,mul_comm (k^_) (k^N),← mul_assoc]
      rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs,abs_of_nonneg hk0] using hk)]
      ring

omit [CompleteSpace F] in
lemma finite_bound {r k C : ℝ} (hr : 0<r) (hrk : r<k) (hC : 0≤C)
    {f : ℕ → E → F}
    (hl : ∀ n x y,dist (f n x) (f n y)≤C*(k/r)^n*dist x y)
    (N : ℕ) (x y : E) (hxy : dist x y≤r^N) :
    dist (∑ n∈Finset.range N,f n x) (∑ n∈Finset.range N,f n y)≤C/(k/r-1)*k^N := by
  have hq : 1<k/r := (one_lt_div hr).mpr hrk
  calc
    _ ≤ ∑ n∈Finset.range N,dist (f n x) (f n y) := dist_sum_sum_le_of_le _ (fun n _ => le_rfl)
    _ ≤ ∑ n∈Finset.range N,C*(k/r)^n*r^N := Finset.sum_le_sum (fun n _ =>
      (hl n x y).trans (mul_le_mul_of_nonneg_left hxy (by positivity)))
    _ = C*r^N*((k/r)^N-1)/(k/r-1) := by
      rw [← Finset.sum_mul,← Finset.mul_sum,geom_sum_eq hq.ne']
      ring
    _ ≤ C*r^N*(k/r)^N/(k/r-1) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by positivity)) (by linarith)
    _ = C/(k/r-1)*k^N := by rw [div_pow]; field_simp

theorem modulus_sum {r k C : ℝ} (hr : 0<r) (hrk : r<k) (hk : k<1) (hC : 0≤C)
    {f : ℕ → E → F}
    (hb : ∀ n x,‖f n x‖≤C*k^n)
    (hl : ∀ n x y,dist (f n x) (f n y)≤C*(k/r)^n*dist x y) :
    (∀ x,Summable (fun n => f n x)) ∧
    ∀ N x y,dist x y≤r^N →
      dist (∑' n,f n x) (∑' n,f n y)≤
        (C/(k/r-1)+2*C/(1-k))*k^N := by
  have hk0 : 0<k := hr.trans hrk
  have hsum (x : E) : Summable (fun n => f n x) := summable_bound hk0.le hk (hb · x)
  refine ⟨hsum,?_⟩
  intro N x y hxy
  have hfin := finite_bound hr hrk hC hl N x y hxy
  have htail (z : E) := tail_bound hk0.le hk (hb · z) N
  rw [← (hsum x).sum_add_tsum_nat_add N,← (hsum y).sum_add_tsum_nat_add N]
  calc
    _ ≤ dist (∑ n∈Finset.range N,f n x) (∑ n∈Finset.range N,f n y)+
        dist (∑' n,f (n+N) x) (∑' n,f (n+N) y) := dist_add_add_le _ _ _ _
    _ ≤ C/(k/r-1)*k^N+(C*k^N/(1-k)+C*k^N/(1-k)) :=
      add_le_add hfin ((dist_le_norm_add_norm _ _).trans (add_le_add (htail x) (htail y)))
    _ = _ := by ring

end ScaleSeries

namespace KernelSeries
open Set MeasureTheory Metric Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma apply_bound (K : 𝓢(E,ℂ)) (hK : ∫ t,K t=0)
    {a C r : ℝ} (ha : 0<a) (ha1 : a≤1) (hC : 0≤C) (hr : 0<r)
    {f : E → ℂ} (hf : Continuous f) (hB : ∃ B,∀ x,‖f x‖≤B)
    (hhold : ∀ x y,dist (f x) (f y)≤C*dist x y^a) (x : E) :
    ‖ScaledKernel.applyKernel K r f x‖≤C*r^a*(∫ t,‖K t‖*‖t‖^a) := by
  have hh := VectorKernelHolder.cancellation_bound K hK ha ha1 hC hr hf hB hhold x
  simpa only [ScaledKernel.applyKernel,smul_eq_mul,mul_comm] using hh

lemma derivative_bound (K : 𝓢(E,ℂ))
    {a C r : ℝ} (ha : 0<a) (ha1 : a≤1) (hC : 0≤C) (hr : 0<r)
    {f : E → ℂ} (hf : Continuous f) (hfi : Integrable f volume)
    (hB : ∃ B,∀ x,‖f x‖≤B)
    (hhold : ∀ x y,dist (f x) (f y)≤C*dist x y^a) (x : E) :
    ‖fderiv ℝ (ScaledKernel.applyKernel K r f) x‖≤
      (C*r^a/r)*(∫ t,‖fderiv ℝ K t‖*‖t‖^a) := by
  rw [(ScaledKernel.derivative K hr hfi x).fderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have hh := VectorKernelHolder.cancellation_bound (SchwartzMap.fderivCLM ℝ E ℂ K)
    (SchwartzKernel.integral_derivative K) ha ha1 hC hr hf hB hhold x
  calc
    _ ≤ r⁻¹*(C*r^a*(∫ t,‖fderiv ℝ K t‖*‖t‖^a)) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hr.le)
    _ = _ := by ring

lemma lipschitz_bound (K : 𝓢(E,ℂ))
    {a C r : ℝ} (ha : 0<a) (ha1 : a≤1) (hC : 0≤C) (hr : 0<r)
    {f : E → ℂ} (hf : Continuous f) (hfi : Integrable f volume)
    (hB : ∃ B,∀ x,‖f x‖≤B)
    (hhold : ∀ x y,dist (f x) (f y)≤C*dist x y^a) (x y : E) :
    dist (ScaledKernel.applyKernel K r f x) (ScaledKernel.applyKernel K r f y)≤
      ((C*r^a/r)*(∫ t,‖fderiv ℝ K t‖*‖t‖^a))*dist x y := by
  simpa only [dist_eq_norm] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z∈(univ : Set E)) => (ScaledKernel.derivative K hr hfi z).differentiableAt)
    (fun z _ => derivative_bound K ha ha1 hC hr hf hfi hB hhold z)
    convex_univ (mem_univ y) (mem_univ x)

theorem holder_sum (K : 𝓢(E,ℂ)) (hK : ∫ t,K t=0)
    {a q : ℝ} (ha : 0<a) (ha1 : a<1) (hq : 0<q) (hq1 : q<1) :
    ∃ T : ℝ,0≤T ∧ ∀ C : ℝ,0≤C → ∀ f : E → ℂ,Continuous f → Integrable f volume →
      (∃ B,∀ x,‖f x‖≤B) → (∀ x y,dist (f x) (f y)≤C*dist x y^a) →
      (∀ x,Summable (fun n : ℕ => ScaledKernel.applyKernel K (q^n) f x)) ∧
      ∀ x y,dist x y≤1 →
        dist (∑' n : ℕ,ScaledKernel.applyKernel K (q^n) f x)
          (∑' n : ℕ,ScaledKernel.applyKernel K (q^n) f y)≤(T*C)*dist x y^a := by
  let k := q^a
  have hk0 : 0<k := Real.rpow_pos_of_pos hq a
  have hqk : q<k := by
    rw [← Real.rpow_one q]
    exact Real.rpow_lt_rpow_of_exponent_gt hq hq1 ha1
  have hk1 : k<1 := Real.rpow_lt_one hq.le hq1 ha
  let J0 := ∫ t,‖K t‖*‖t‖^a
  let J1 := ∫ t,‖fderiv ℝ K t‖*‖t‖^a
  have hJ0 : 0≤J0 := integral_nonneg (fun _ => by positivity)
  have hJ1 : 0≤J1 := integral_nonneg (fun _ => by positivity)
  let J := max J0 J1
  have hJ : 0≤J := hJ0.trans (le_max_left _ _)
  let T := (J/(k/q-1)+2*J/(1-k))/k
  have hkq : 1<k/q := (one_lt_div hq).mpr hqk
  have hT : 0≤T := by dsimp only [T]; positivity
  refine ⟨T,hT,?_⟩
  intro C hC f hf hfi hB hhold
  have hb (n : ℕ) (x : E) : ‖ScaledKernel.applyKernel K (q^n) f x‖≤(C*J)*k^n := by
    have hh := apply_bound K hK ha ha1.le hC (pow_pos hq n) hf hB hhold x
    rw [ GridHolder.pow_rpow hq.le (show q^a=k from rfl)] at hh
    change _≤C*k^n*J0 at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (le_max_left J0 J1) (mul_nonneg hC (pow_nonneg hk0.le n))])
  have hl (n : ℕ) (x y : E) : dist (ScaledKernel.applyKernel K (q^n) f x) (ScaledKernel.applyKernel K (q^n) f y)≤
      (C*J)*(k/q)^n*dist x y := by
    have hh := lipschitz_bound K ha ha1.le hC (pow_pos hq n) hf hfi hB hhold x y
    rw [GridHolder.pow_rpow hq.le (show q^a=k from rfl)] at hh
    apply hh.trans
    change (C*k^n/q^n*J1)*_≤_
    rw [div_pow]
    have hj := mul_le_mul_of_nonneg_left (le_max_right J0 J1) (show 0≤C*k^n/q^n by positivity)
    calc
      _ ≤ (C*k^n/q^n*J)*dist x y := mul_le_mul_of_nonneg_right hj dist_nonneg
      _ = _ := by ring
  obtain ⟨hSum,hMod⟩ := ScaleSeries.modulus_sum hq hqk hk1 (mul_nonneg hC hJ) hb hl
  refine ⟨hSum,?_⟩
  have hh := GridHolder.of_grid hq (hqk.trans hk1) hk0 ha (show q^a=k from rfl)
    (show 0≤C*J/(k/q-1)+2*(C*J)/(1-k) by positivity) zero_lt_one (by simpa only [one_mul] using hMod)
  intro x y hxy
  convert hh x y hxy using 1
  dsimp only [T]
  simp only [div_one]
  ring
end KernelSeries
namespace AnnularFourier
open Set MeasureTheory FourierTransform Filter LineDeriv Metric
open scoped SchwartzMap InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

lemma decompose (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) (u : 𝓢(E,ℂ)) (x : E)
    (hSum : Summable (fun n : ℕ => ScaledKernel.applyKernel (AnnularSymbol.kernel A hA v w)
      ((1/2:ℝ)^n) (elliptic b A u) x)) :
    (∂_{v} (∂_{w} u)) x=lowFilter (∂_{v} (∂_{w} u)) 1 one_ne_zero x+
      ∑' n : ℕ,ScaledKernel.applyKernel (AnnularSymbol.kernel A hA v w) ((1/2:ℝ)^n) (elliptic b A u) x := by
  let H := ∂_{v} (∂_{w} u)
  let K := AnnularSymbol.kernel A hA v w
  let F := fun n : ℕ => lowFilter H ((1/2:ℝ)^n) (pow_ne_zero _ (by norm_num)) x
  have hn (n : ℕ) : ScaledKernel.applyKernel K ((1/2:ℝ)^n) (elliptic b A u) x=F (n+1)-F n := by
    rw [← normalized_conv _ _ (pow_pos (by norm_num : (0:ℝ)<1/2) _),annular_identity (hr := pow_pos (by norm_num : (0:ℝ)<1/2) n), piece_telescope]
    rfl
  have htel (N : ℕ) : (∑ n∈Finset.range N,ScaledKernel.applyKernel K ((1/2:ℝ)^n) (elliptic b A u) x)=F N-F 0 := by
    simp_rw [hn]
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih]; abel
  have hlim : Tendsto F atTop (𝓝 (H x)) := lowFilter_tendsto H _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)) x
  change Summable (fun n:ℕ => ScaledKernel.applyKernel K ((1/2:ℝ)^n) (elliptic b A u) x) at hSum
  have he := tendsto_nhds_unique hSum.hasSum.tendsto_sum_nat
    (by simpa only [htel] using hlim.sub_const (F 0))
  change _=H x-F 0 at he
  change H x=F 0+_
  rw [he]
  abel

omit [Fintype ι] in
lemma lowFilter_eq_kernel (u : 𝓢(E,ℂ)) (x : E) :
    lowFilter u 1 one_ne_zero x=ScaledKernel.applyKernel (lowKernel : 𝓢(E,ℂ)) 1 u x := by
  rw [← normalized_conv _ _ zero_lt_one]
  have he : 𝓕 (conv (normalized (lowKernel : 𝓢(E,ℂ)) 1 one_ne_zero) u)=
      product (ScaledKernel.dilate lowSymbol 1 one_ne_zero) (𝓕 u) := by
    ext y
    rw [fourier_conv,product_apply,fourier_normalized _ zero_lt_one,
      lowKernel,fourier_fourierInv_eq,product_apply,ScaledKernel.dilate_apply]
  have hh := congrArg (fun f : 𝓢(E,ℂ) => 𝓕⁻ f) he
  rw [fourierInv_fourier_eq] at hh
  exact congrArg (fun f : 𝓢(E,ℂ) => f x) hh.symm

omit [Fintype ι] in
lemma lowFilter_lipschitz (u : 𝓢(E,ℂ)) {B : ℝ} (hB : ∀ x,‖u x‖≤B) (x y : E) :
    dist (lowFilter u 1 one_ne_zero x) (lowFilter u 1 one_ne_zero y)≤
      (B*∫ t,‖fderiv ℝ (lowKernel : 𝓢(E,ℂ)) t‖)*dist x y := by
  let K : 𝓢(E,ℂ) := lowKernel
  have hfun : (fun x => lowFilter u 1 one_ne_zero x)=ScaledKernel.applyKernel K 1 u :=
    funext (lowFilter_eq_kernel u)
  have hd (z : E) := ScaledKernel.derivative K zero_lt_one u.integrable z
  have hb (z : E) : ‖fderiv ℝ (ScaledKernel.applyKernel K 1 u) z‖≤B*∫ t,‖fderiv ℝ K t‖ := by
    rw [(hd z).fderiv]
    simp only [inv_one,one_smul]
    calc
      _ ≤ ∫ t,‖u (z-t) • fderiv ℝ K t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t,B*‖fderiv ℝ K t‖ := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          ((SchwartzMap.fderivCLM ℝ E ℂ K).integrable.norm.const_mul B)
        filter_upwards with t
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  rw [show lowFilter u 1 one_ne_zero x=ScaledKernel.applyKernel K 1 u x from congrFun hfun x,
    show lowFilter u 1 one_ne_zero y=ScaledKernel.applyKernel K 1 u y from congrFun hfun y]
  simpa only [dist_eq_norm] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z∈(univ : Set E)) => (hd z).differentiableAt) (fun z _ => hb z)
    convex_univ (mem_univ y) (mem_univ x)

theorem schwartz_schauder (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ T : ℝ,0≤T ∧ ∀ (u : 𝓢(E,ℂ)) (C B : ℝ),0≤C → 0≤B →
      (∀ x,‖(∂_{v} (∂_{w} u)) x‖≤B) →
      (∀ x y,dist (elliptic b A u x) (elliptic b A u y)≤C*dist x y^a) →
      ∀ x y,dist x y≤1 → dist ((∂_{v} (∂_{w} u)) x) ((∂_{v} (∂_{w} u)) y)≤
        T*(B+C)*dist x y^a := by
  let K := AnnularSymbol.kernel A hA v w
  have hK : ∫ t,K t=0 := by
    dsimp only [K,AnnularSymbol.kernel]
    rw [SchwartzKernel.integral_fourierInv,AnnularSymbol.symbol_zero]
  obtain ⟨T,hT,hSeries⟩ := KernelSeries.holder_sum K hK ha ha1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let J := ∫ t,‖fderiv ℝ (lowKernel : 𝓢(E,ℂ)) t‖
  have hJ : 0≤J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨max J T,le_max_of_le_left hJ,?_⟩
  intro u C B hC hB hUb hHold x y hxy
  obtain ⟨hSum,hHolder⟩ := hSeries C hC (elliptic b A u) (elliptic b A u).continuous
    (elliptic b A u).integrable ⟨SchwartzMap.seminorm ℝ 0 0 (elliptic b A u),
      (elliptic b A u).norm_le_seminorm ℝ⟩ hHold
  rw [decompose b A hA v w u x (hSum x),decompose b A hA v w u y (hSum y)]
  apply (dist_add_add_le _ _ _ _).trans
  have hLow := lowFilter_lipschitz (∂_{v} (∂_{w} u)) hUb x y
  have hHigh := hHolder x y hxy
  have hd : dist x y≤dist x y^a := by
    by_cases h0 : dist x y=0
    · rw [h0,Real.zero_rpow (ne_of_gt ha)]
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne dist_nonneg (Ne.symm h0)) hxy ha1.le
  have hb := mul_le_mul_of_nonneg_left hd (mul_nonneg hB hJ)
  have hj := mul_le_mul_of_nonneg_left (le_max_left J T) hB
  have ht := mul_le_mul_of_nonneg_left (le_max_right J T) hC
  change _≤B*J*dist x y at hLow
  apply (add_le_add (hLow.trans hb) hHigh).trans
  nlinarith [mul_le_mul_of_nonneg_right hj (Real.rpow_nonneg (dist_nonneg : 0≤dist x y) a),
    mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (dist_nonneg : 0≤dist x y) a)]
end AnnularFourier
namespace KernelCommutator
open Set MeasureTheory Metric Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_mul (K : 𝓢(E,ℂ)) {f : E → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x,‖f x‖≤B) (r : ℝ) (x : E) :
    Integrable (fun t => K t*f (x-r • t)) volume := by
  apply (K.integrable.norm.mul_const B).mono'
    ((K.continuous.mul (hf.comp (continuous_const.sub (continuous_const.smul continuous_id)))).aestronglyMeasurable)
  filter_upwards with t
  change ‖K t*f (x-r • t)‖≤‖K t‖*B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

lemma apply_bound (K : 𝓢(E,ℂ)) {f : E → ℂ} {B : ℝ}
    (hB : ∀ x,‖f x‖≤B) (r : ℝ) (x : E) :
    ‖ScaledKernel.applyKernel K r f x‖≤B*∫ t,‖K t‖ := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ t,‖K t*f (x-r • t)‖)≤∫ t,B*‖K t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (K.integrable.norm.const_mul B)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

end KernelCommutator
namespace ScaledKernel
open Set MeasureTheory Metric Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma holder_apply (K : 𝓢(E,ℂ)) {f : E → ℂ} (hf : Continuous f)
    {a C B r : ℝ} (hB : ∀ x,‖f x‖≤B)
    (hhold : ∀ x y,dist (f x) (f y)≤C*dist x y^a) (x y : E) :
    dist (applyKernel K r f x) (applyKernel K r f y)≤
      (C*∫ t,‖K t‖)*dist x y^a := by
  rw [dist_eq_norm,applyKernel,applyKernel,← integral_sub
    (KernelCommutator.integrable_mul K hf hB r x) (KernelCommutator.integrable_mul K hf hB r y)]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ t,‖K t*f (x-r • t)-K t*f (y-r • t)‖)≤∫ t,(C*dist x y^a)*‖K t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (K.integrable.norm.const_mul _)
      filter_upwards with t
      rw [← mul_sub,norm_mul]
      have hh := hhold (x-r • t) (y-r • t)
      rw [dist_sub_right,dist_eq_norm (f _) (f _)] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by rw [integral_const_mul]; ring

lemma apply_tendsto (K : 𝓢(E,ℂ)) (hK : ∫ t,K t=1) {f : E → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x,‖f x‖≤B) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => applyKernel K (r n) f x) atTop (𝓝 (f x)) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := (volume : Measure E))
    (F := fun (n:ℕ) (t:E) => K t*f (x-r n • t)) (f := fun t:E => K t*f x)
    (fun t:E => ‖K t‖*B)
    (fun n => (KernelCommutator.integrable_mul K hf hB (r n) x).aestronglyMeasurable)
    (K.integrable.norm.mul_const B)
    (fun n => Filter.Eventually.of_forall (fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)))
    (Filter.Eventually.of_forall (fun t:E => by
      have ht : Tendsto (fun n => x-r n • t) atTop (𝓝 x) := by
        simpa only [zero_smul,sub_zero] using tendsto_const_nhds.sub (hr.smul_const t)
      exact tendsto_const_nhds.mul ((hf.tendsto x).comp ht)))
  rw [integral_mul_const,hK,one_mul] at hh
  exact hh
end ScaledKernel
namespace CompactMollification
section
open Set MeasureTheory Metric Filter LineDeriv
open scoped SchwartzMap Topology InnerProductSpace Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma conv_eq (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) (u : E → ℂ) :
    (AnnularFourier.normalized K r hr.ne' ⋆[ContinuousLinearMap.mul ℝ ℂ] u)=
      ScaledKernel.applyKernel K r u := by
  ext x
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply',AnnularFourier.normalized,smul_apply,
    ScaledKernel.dilate_apply,smul_mul_assoc]
  rw [integral_smul]
  have hh := Measure.integral_comp_smul_of_nonneg (volume:Measure E)
    (fun t => K (r⁻¹ • t)*u (x-t)) r (hR:=hr.le)
  rw [← hh]
  simp only [inv_smul_smul₀ hr.ne',ScaledKernel.applyKernel]

omit [MeasurableSpace E] [BorelSpace E] in
lemma normalized_compact (K : 𝓢(E,ℂ)) (hK : HasCompactSupport (K : E → ℂ))
    {r : ℝ} (hr : r≠0) : HasCompactSupport (AnnularFourier.normalized K r hr : E → ℂ) :=
  (hK.comp_smul (inv_ne_zero hr)).smul_left

lemma apply_compact (K : 𝓢(E,ℂ)) (hK : HasCompactSupport (K : E → ℂ))
    {r : ℝ} (hr : 0<r) {u : E → ℂ} (hu : HasCompactSupport u) :
    HasCompactSupport (ScaledKernel.applyKernel K r u) := by
  rw [← conv_eq K hr u]
  exact (normalized_compact K hK hr.ne').convolution _ hu

lemma apply_smooth (K : 𝓢(E,ℂ)) (hK : HasCompactSupport (K : E → ℂ))
    {r : ℝ} (hr : 0<r) {u : E → ℂ} (hu : Continuous u) :
    ContDiff ℝ ∞ (ScaledKernel.applyKernel K r u) := by
  rw [← conv_eq K hr u]
  exact (normalized_compact K hK hr.ne').contDiff_convolution_left _
    ((AnnularFourier.normalized K r hr.ne').smooth ⊤) hu.locallyIntegrable

lemma apply_derivative (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r)
    {u : E → ℂ} (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (v x : E) :
    fderiv ℝ (ScaledKernel.applyKernel K r u) x v=
      ScaledKernel.applyKernel K r (fun z => fderiv ℝ u z v) x := by
  rw [← conv_eq K hr u]
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (AnnularFourier.normalized K r hr.ne').integrable.locallyIntegrable hu x).fderiv]
  rw [convolution_precompR_apply _ (AnnularFourier.normalized K r hr.ne').integrable.locallyIntegrable
    (hc.fderiv ℝ) (hu.continuous_fderiv one_ne_zero),conv_eq K hr]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_compact {u : E → ℂ} (hc : HasCompactSupport u) (v : E) :
    HasCompactSupport (fun z => fderiv ℝ u z v) :=
  (hc.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T v) (by simp)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_C1 {u : E → ℂ} (hu : ContDiff ℝ 2 u) (v : E) :
    ContDiff ℝ 1 (fun z => fderiv ℝ u z v) :=
  (hu.fderiv_right (by norm_num)).clm_apply contDiff_const

lemma apply_second (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r)
    {u : E → ℂ} (hc : HasCompactSupport u) (hu : ContDiff ℝ 2 u) (v w x : E) :
    dd (ScaledKernel.applyKernel K r u) v w x=ScaledKernel.applyKernel K r (dd u v w) x := by
  unfold dd
  rw [show (fun z => fderiv ℝ (ScaledKernel.applyKernel K r u) z w)=
    ScaledKernel.applyKernel K r (fun z => fderiv ℝ u z w) from
      funext (apply_derivative K hr hc (hu.of_le (by norm_num)) w)]
  exact apply_derivative K hr (derivative_compact hc w) (derivative_C1 hu w) v x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dd_continuous {u : E → ℂ} (hu : ContDiff ℝ 2 u) (v w : E) :
    Continuous (dd u v w) :=
  ((derivative_C1 hu w).continuous_fderiv one_ne_zero).clm_apply continuous_const
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dd_compact {u : E → ℂ} (hc : HasCompactSupport u) (v w : E) :
    HasCompactSupport (dd u v w) := derivative_compact (derivative_compact hc w) v
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dd_schwartz (u : 𝓢(E,ℂ)) (v w x : E) :
    (∂_{v} (∂_{w} u)) x=dd u v w x := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [show ((∂_{w} u : 𝓢(E,ℂ)) : E → ℂ)=(fun z => fderiv ℝ u z w) from
    funext (fun z => SchwartzMap.lineDerivOp_apply_eq_fderiv w u z)]
  rfl

lemma mollifier_compact : HasCompactSupport (mollifier : E → ℂ) :=
  ((AnnularFourier.lowBump (E:=E)).hasCompactSupport_normed (μ:=volume)).comp_left
    (by simp : Complex.ofReal (0:ℝ)=0)
lemma mollifier_integral : ∫ t:E,mollifier t=1 := by
  have hh := Complex.ofRealCLM.integral_comp_comm ((AnnularFourier.lowBump (E:=E)).integrable_normed (μ:=volume))
  rw [(AnnularFourier.lowBump (E:=E)).integral_normed] at hh
  exact hh
lemma mollifier_norm : ∫ t:E,‖mollifier t‖=1 := by
  change (∫ t:E,‖Complex.ofReal ((AnnularFourier.lowBump (E:=E)).normed volume t)‖)=1
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    ((AnnularFourier.lowBump (E:=E)).nonneg_normed (μ:=volume) _)]
  exact (AnnularFourier.lowBump (E:=E)).integral_normed
end
open Set MeasureTheory Metric Filter LineDeriv
open scoped SchwartzMap Topology InnerProductSpace Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma bounded_compact {f : E → ℂ} (hc : HasCompactSupport f) (hf : Continuous f) :
    ∃ B : ℝ,∀ x,‖f x‖≤B := by
  obtain ⟨B,hB⟩ := hf.norm.bddAbove_range_of_hasCompactSupport
    (hc.comp_left (g := fun z : ℂ => ‖z‖) (norm_zero))
  exact ⟨B,fun x => hB (mem_range_self x)⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma elliptic_continuous (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    {u : E → ℂ} (hu : ContDiff ℝ 2 u) : Continuous (elliptic b A u) :=
  continuous_finsetSum _ (fun i _ => dd_continuous hu (b i) (A (b i)))
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma elliptic_compact (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    {u : E → ℂ} (hc : HasCompactSupport u) : HasCompactSupport (elliptic b A u) :=
  by
    change HasCompactSupport (fun x => ∑ i,dd u (b i) (A (b i)) x)
    have ht := HasCompactSupport.finset_sum
      (s := Finset.univ) (f := fun i => dd u (b i) (A (b i)))
      (fun i _ => dd_compact hc (b i) (A (b i)))
    have heq : (∑ i, dd u (b i) (A (b i))) = (fun x => ∑ i, dd u (b i) (A (b i)) x) := by
      ext x
      simp only [Finset.sum_apply]
    rw [heq] at ht
    exact ht
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma elliptic_schwartz (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (u : 𝓢(E,ℂ)) (x : E) :
    AnnularFourier.elliptic b A u x=elliptic b A u x := by
  simp only [AnnularFourier.elliptic,elliptic,sum_apply,dd_schwartz]

lemma apply_elliptic (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (K : 𝓢(E,ℂ)) {r : ℝ} (hr : 0<r) {u : E → ℂ}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 2 u) (x : E) :
    elliptic b A (ScaledKernel.applyKernel K r u) x=ScaledKernel.applyKernel K r (elliptic b A u) x := by
  simp only [elliptic,apply_second K hr hc hu,ScaledKernel.applyKernel,Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  obtain ⟨B,hB⟩ := bounded_compact (dd_compact hc (b i) (A (b i))) (dd_continuous hu (b i) (A (b i)))
  exact KernelCommutator.integrable_mul K (dd_continuous hu (b i) (A (b i))) hB r x

theorem compact_schauder (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ T : ℝ,0≤T ∧ ∀ (u : E → ℂ),HasCompactSupport u → ContDiff ℝ 2 u →
      ∀ (C B : ℝ),0≤C → 0≤B → (∀ x,‖dd u v w x‖≤B) →
      (∀ x y,dist (elliptic b A u x) (elliptic b A u y)≤C*dist x y^a) →
      ∀ x y,dist x y≤1 → dist (dd u v w x) (dd u v w y)≤T*(B+C)*dist x y^a := by
  obtain ⟨T,hT,hSmooth⟩ := AnnularFourier.schwartz_schauder b A hA v w ha ha1
  refine ⟨T,hT,?_⟩
  intro u hc hu C B hC hB hBound hHolder x y hxy
  let K : 𝓢(E,ℂ) := mollifier
  let r : ℕ → ℝ := fun n => (1/2:ℝ)^n
  have hr (n : ℕ) : 0<r n := pow_pos (by norm_num) n
  let un (n : ℕ) : 𝓢(E,ℂ) :=
    (apply_compact K mollifier_compact (hr n) hc).toSchwartzMap
      (apply_smooth K mollifier_compact (hr n) hu.continuous)
  have hdd (n : ℕ) (z : E) : (∂_{v} (∂_{w} (un n))) z=ScaledKernel.applyKernel K (r n) (dd u v w) z := by
    rw [dd_schwartz]
    exact apply_second K (hr n) hc hu v w z
  have hel (n : ℕ) (z : E) : AnnularFourier.elliptic b A (un n) z=
      ScaledKernel.applyKernel K (r n) (elliptic b A u) z := by
    rw [elliptic_schwartz]
    exact apply_elliptic b A K (hr n) hc hu z
  obtain ⟨BL,hBL⟩ := bounded_compact (elliptic_compact b A hc) (elliptic_continuous b A hu)
  have he (n : ℕ) : dist (ScaledKernel.applyKernel K (r n) (dd u v w) x)
      (ScaledKernel.applyKernel K (r n) (dd u v w) y)≤T*(B+C)*dist x y^a := by
    rw [← hdd n x,← hdd n y]
    apply hSmooth (un n) C B hC hB _ _ x y hxy
    · intro z
      rw [hdd]
      have hh := KernelCommutator.apply_bound K hBound (r n) z
      simpa only [K,mollifier_norm,mul_one] using hh
    · intro z t
      rw [hel,hel]
      have hh := ScaledKernel.holder_apply K (elliptic_continuous b A hu) hBL hHolder (r:=r n) z t
      simpa only [K,mollifier_norm,mul_one] using hh
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  have hlx := ScaledKernel.apply_tendsto K mollifier_integral (dd_continuous hu v w) hBound hlim x
  have hly := ScaledKernel.apply_tendsto K mollifier_integral (dd_continuous hu v w) hBound hlim y
  exact le_of_tendsto (hlx.dist hly) (Filter.Eventually.of_forall he)
end CompactMollification

namespace ScalarInterpolation
open Set Metric
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_bound {f g H : ℝ → F} {r B M : ℝ} (hr : 0<r)
    (hf : ∀ t∈Icc (-r) r,HasDerivAt f (g t) t)
    (hg : ∀ t∈Icc (-r) r,HasDerivAt g (H t) t)
    (hH : ∀ t∈Icc (-r) r,‖H t-H 0‖≤M)
    (hB : ∀ t∈Icc (-r) r,‖f t‖≤B) :
    ‖H 0‖≤4*B/r^2+2*M := by
  have h0 : (0:ℝ)∈Icc (-r) r := ⟨by linarith,hr.le⟩
  let G := fun t => g t-g 0-t • H 0
  have hdG (t : ℝ) (ht : t∈Icc (-r) r) : HasDerivAt G (H t-H 0) t := by
    convert ((hg t ht).sub_const (g 0)).sub ((hasDerivAt_id t).smul_const (H 0)) using 1
    · rfl
    · simp only [one_smul]
  have hbG (t : ℝ) (ht : t∈Icc (-r) r) : ‖G t‖≤M*r := by
    have hh := (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hdG z hz).hasDerivWithinAt) (fun z hz => hH z hz) h0 ht
    have htabs : |t|≤r := abs_le.mpr ht
    have hM : 0≤M := by simpa only [sub_self,norm_zero] using hH 0 h0
    have hzero : G 0=0 := by simp [G]
    rw [hzero,sub_zero,sub_zero,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left htabs hM)
  let R := fun t => f t-f 0-t • g 0-(t^2/2) • H 0
  have hdR (t : ℝ) (ht : t∈Icc (-r) r) : HasDerivAt R (G t) t := by
    have hquad : HasDerivAt (fun t:ℝ => t^2/2) t t := by
      have hh := ((hasDerivAt_id t).pow 2).div_const (2:ℝ)
      simpa using hh
    convert (((hf t ht).sub_const (f 0)).sub ((hasDerivAt_id t).smul_const (g 0))).sub
      (hquad.smul_const (H 0)) using 1
    · rfl
    · simp only [G, one_smul]
  have hbR (t : ℝ) (ht : t∈Icc (-r) r) : ‖R t‖≤M*r^2 := by
    have hh := (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hdR z hz).hasDerivWithinAt) (fun z hz => hbG z hz) h0 ht
    have htabs : |t|≤r := abs_le.mpr ht
    have hM : 0≤M := by simpa only [sub_self,norm_zero] using hH 0 h0
    have hzero : R 0=0 := by simp [R]
    rw [hzero,sub_zero,sub_zero,Real.norm_eq_abs] at hh
    have hm := mul_le_mul_of_nonneg_left htabs (mul_nonneg hM hr.le)
    nlinarith
  have hp : r∈Icc (-r) r := ⟨by linarith,le_rfl⟩
  have hn : -r∈Icc (-r) r := ⟨le_rfl,by linarith⟩
  have he : r^2 • H 0=f r+f (-r)-(2:ℝ) • f 0-(R r+R (-r)) := by
    simp only [R,neg_smul,neg_sq,sub_eq_add_neg]
    module
  have hnrm := norm_add_le (R r) (R (-r))
  have hff := norm_add_le (f r) (f (-r))
  have h2 : ‖(2:ℝ) • f 0‖=2*‖f 0‖ := by rw [norm_smul]; norm_num
  have ht := norm_sub_le (f r+f (-r)-(2:ℝ) • f 0) (R r+R (-r))
  have ht2 := norm_sub_le (f r+f (-r)) ((2:ℝ) • f 0)
  have hnorm : ‖r^2 • H 0‖=r^2*‖H 0‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  rw [← he,hnorm] at ht
  rw [h2] at ht2
  have hpB := hB r hp
  have hnB := hB (-r) hn
  have h0B := hB 0 h0
  have hpR := hbR r hp
  have hnR := hbR (-r) hn
  have hh : r^2*‖H 0‖≤4*B+2*M*r^2 := by linarith
  calc
    _ ≤ (4*B+2*M*r^2)/r^2 := by apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr; nlinarith only [hh]
    _ = _ := by field_simp
end ScalarInterpolation
namespace HessianInterpolation
section
open Set Metric
open scoped ContDiff
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ray_second {u : E → F} (hu : ContDiff ℝ 2 u) (x v : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ u (x+t • v) v)
      (hessian u (x+t • v) v v) t := by
  have hd : Differentiable ℝ (fderiv ℝ u) := (hu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable one_ne_zero
  have hh := ((hd (x+t • v)).hasFDerivAt.clm_apply (hasFDerivAt_const v (x+t • v))).comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x)
  simpa [Function.comp_def, hessian] using hh

lemma diagonal_bound {u : E → F} (hu : ContDiff ℝ 2 u) {B S a r : ℝ}
    (_hB : 0≤B) (hS : 0≤S) (ha : 0≤a) (hr : 0<r)
    (hb : ∀ x,‖u x‖≤B)
    (hh : ∀ x y,dist (hessian u x) (hessian u y)≤S*dist x y^a) (x v : E) (hv : ‖v‖≤2) :
    ‖hessian u x v v‖≤4*B/r^2+8*S*(2*r)^a := by
  have hd (t : ℝ) : HasDerivAt (fun t:ℝ => u (x+t • v)) (fderiv ℝ u (x+t • v) v) t := by
    have ht := ((hu.differentiable (by norm_num : (2:WithTop ℕ∞)≠0)) (x+t • v)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add x)
    simpa only [one_smul, Function.comp_def, id_eq] using ht
  have hosc (t : ℝ) (ht : t∈Icc (-r) r) :
      ‖hessian u (x+t • v) v v-hessian u (x+(0:ℝ) • v) v v‖≤4*S*(2*r)^a := by
    simp only [zero_smul,add_zero]
    have hdxy : dist (x+t • v) x≤2*r := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
      nlinarith [abs_le.mpr ht,abs_nonneg t,norm_nonneg v]
    have hh' := hh (x+t • v) x
    rw [dist_eq_norm (hessian u _) (hessian u _)] at hh'
    have hdp := Real.rpow_le_rpow dist_nonneg hdxy ha
    have hh'' : ‖hessian u (x+t • v)-hessian u x‖≤S*(2*r)^a :=
      hh'.trans (mul_le_mul_of_nonneg_left hdp hS)
    have he : hessian u (x+t • v) v v-hessian u x v v=(hessian u (x+t • v)-hessian u x) v v := rfl
    rw [he]
    have h1 := ((hessian u (x+t • v)-hessian u x) v).le_opNorm v
    have h2 := (hessian u (x+t • v)-hessian u x).le_opNorm v
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    have hn : ‖v‖^2≤4 := by nlinarith [norm_nonneg v]
    calc
      _ ≤ ‖hessian u (x+t • v)-hessian u x‖*‖v‖^2 := by nlinarith only [h1,h3]
      _ ≤ (S*(2*r)^a)*‖v‖^2 := mul_le_mul_of_nonneg_right hh'' (sq_nonneg _)
      _ ≤ (S*(2*r)^a)*4 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  have hs := ScalarInterpolation.second_bound hr (fun t _ => hd t)
    (fun t _ => ray_second hu x v t) hosc (fun t _ => hb (x+t • v))
  simpa only [zero_smul,add_zero,show 2*(4*S*(2*r)^a)=8*S*(2*r)^a by ring] using hs

theorem norm_bound {u : E → F} (hu : ContDiff ℝ 2 u) {B S a r : ℝ}
    (hB : 0≤B) (hS : 0≤S) (ha : 0≤a) (hr : 0<r)
    (hb : ∀ x,‖u x‖≤B)
    (hh : ∀ x y,dist (hessian u x) (hessian u y)≤S*dist x y^a) (x : E) :
    ‖hessian u x‖≤2*B/r^2+4*S*(2*r)^a := by
  have hC : 0≤2*B/r^2+4*S*(2*r)^a := by positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro w hw
  have hp := diagonal_bound hu hB hS ha hr hb hh x (v+w) (by simpa [hv,hw,show (1:ℝ)+1=2 by norm_num] using norm_add_le v w)
  have hm := diagonal_bound hu hB hS ha hr hb hh x (v-w) (by simpa [hv,hw,show (1:ℝ)+1=2 by norm_num] using norm_sub_le v w)
  have hsym : hessian u x v w=hessian u x w v :=
    hu.contDiffAt.isSymmSndFDerivAt (by norm_num) v w
  have he : (4:ℝ) • hessian u x v w=hessian u x (v+w) (v+w)-hessian u x (v-w) (v-w) := by
    simp only [map_add,map_sub,add_apply,sub_apply]
    rw [← hsym]
    module
  have hn := norm_sub_le (hessian u x (v+w) (v+w)) (hessian u x (v-w) (v-w))
  rw [← he,norm_smul] at hn
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<4)] at hn
  simp only [div_eq_mul_inv] at hp hm ⊢
  linarith
end
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

lemma bilinear_norm_bound (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E →L[ℝ] F)
    {B : ℝ} (hB : 0≤B) (hb : ∀ i j,‖T (b i) (b j)‖≤B) :
    ‖T‖≤(Fintype.card ι:ℝ)^2*B := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have he : T v w=∑ i,∑ j,((b.repr v) i*(b.repr w) j) • T (b i) (b j) := by
    calc
      _ = T (∑ i,(b.repr v) i • b i) (∑ j,(b.repr w) j • b j) := by rw [b.sum_repr,b.sum_repr]
      _ = _ := by
        simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.smul_sum,smul_smul]
        rw [Finset.sum_comm]
        simp only [mul_comm]
  have hvc (i : ι) : ‖(b.repr v) i‖≤1 := by
    simpa only [OrthonormalBasis.repr_apply_apply,Real.norm_eq_abs,b.orthonormal.norm_eq_one,hv,mul_one] using
      abs_real_inner_le_norm (b i) v
  have hwc (i : ι) : ‖(b.repr w) i‖≤1 := by
    simpa only [OrthonormalBasis.repr_apply_apply,Real.norm_eq_abs,b.orthonormal.norm_eq_one,hw,mul_one] using
      abs_real_inner_le_norm (b i) w
  rw [he]
  calc
    _ ≤ ∑ i,∑ j,‖((b.repr v) i*(b.repr w) j) • T (b i) (b j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i:ι,∑ _j:ι,B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,norm_mul]
      have hprod : ‖(b.repr v) i‖*‖(b.repr w) j‖≤1 := by nlinarith [norm_nonneg ((b.repr v) i),norm_nonneg ((b.repr w) j),hvc i,hwc j]
      exact (mul_le_mul_of_nonneg_right hprod (norm_nonneg _)).trans (by simpa only [one_mul] using hb i j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end HessianInterpolation
namespace CompactMollification
open Set MeasureTheory Metric Filter LineDeriv
open scoped SchwartzMap Topology InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dd_hessian {u : E → ℂ} (hu : ContDiff ℝ 2 u) (v w x : E) :
    dd u v w x=HessianInterpolation.hessian u x v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable one_ne_zero) x
  have hh := hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  change fderiv ℝ (fun z => fderiv ℝ u z w) x v=_
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply,HessianInterpolation.hessian]

theorem hessian_schauder (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ T : ℝ,0<T ∧ ∀ (u : E → ℂ),HasCompactSupport u → ContDiff ℝ 2 u →
      ∀ (C B : ℝ),0≤C → 0≤B → (∀ x,‖HessianInterpolation.hessian u x‖≤B) →
      (∀ x y,dist (elliptic b A u x) (elliptic b A u y)≤C*dist x y^a) →
      ∀ x y,dist (HessianInterpolation.hessian u x) (HessianInterpolation.hessian u y)≤
        T*(B+C)*dist x y^a := by
  classical
  choose T hT hS using fun (i j:ι) => compact_schauder b A hA (b i) (b j) ha ha1
  let T0 : ℝ := ∑ i,∑ j,T i j
  have hT0 : 0≤T0 := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hT i j))
  have hTi (i j : ι) : T i j≤T0 :=
    (Finset.single_le_sum (fun k _ => hT i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hT k l)) (Finset.mem_univ i))
  refine ⟨(Fintype.card ι:ℝ)^2*T0+2,by positivity,?_⟩
  intro u hc hu C B hC hB hBound hHolder x y
  have hpow := Real.rpow_nonneg (dist_nonneg : 0≤dist x y) a
  by_cases hxy : dist x y≤1
  · rw [dist_eq_norm (HessianInterpolation.hessian u x)]
    have hcomp (i j : ι) : ‖(HessianInterpolation.hessian u x-HessianInterpolation.hessian u y) (b i) (b j)‖≤
        (T0*(B+C)*dist x y^a) := by
      have hb (z : E) : ‖dd u (b i) (b j) z‖≤B := by
        rw [dd_hessian hu]
        apply (((HessianInterpolation.hessian u z) (b i)).le_opNorm (b j)).trans
        have hn := (HessianInterpolation.hessian u z).le_opNorm (b i)
        simp only [b.orthonormal.norm_eq_one,mul_one] at hn ⊢
        exact hn.trans (hBound z)
      have hh := hS i j u hc hu C B hC hB hb hHolder x y hxy
      rw [dist_eq_norm,dd_hessian hu,dd_hessian hu] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hTi i j) (add_nonneg hB hC)) hpow)
    have hh := HessianInterpolation.bilinear_norm_bound b
      (HessianInterpolation.hessian u x-HessianInterpolation.hessian u y) (by positivity) hcomp
    apply hh.trans
    have hp : 0≤(B+C)*dist x y^a := mul_nonneg (add_nonneg hB hC) hpow
    nlinarith
  · have hge : 1≤dist x y^a := Real.one_le_rpow (le_of_lt (lt_of_not_ge hxy)) ha.le
    have hd := dist_le_norm_add_norm (HessianInterpolation.hessian u x) (HessianInterpolation.hessian u y)
    have hm := mul_le_mul_of_nonneg_left hge (show 0≤B+C by positivity)
    have hn : 0≤(Fintype.card ι:ℝ)^2*T0 := by positivity
    have hn2 := mul_nonneg hn (show 0≤(B+C)*dist x y^a by positivity)
    nlinarith [hBound x,hBound y]
end CompactMollification
namespace CoefficientTrace
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
lemma sub_left (b : OrthonormalBasis ι ℝ E) (H G : E →L[ℝ] E →L[ℝ] F) (A : E →L[ℝ] E) :
    trace b (H-G) A=trace b H A-trace b G A := by
  simp only [trace,sub_apply,Finset.sum_sub_distrib]
lemma sub_right (b : OrthonormalBasis ι ℝ E) (H : E →L[ℝ] E →L[ℝ] F) (A B : E →L[ℝ] E) :
    trace b H (A-B)=trace b H A-trace b H B := by
  simp only [trace,sub_apply,map_sub,Finset.sum_sub_distrib]
lemma variation (b : OrthonormalBasis ι ℝ E) (H G : E →L[ℝ] E →L[ℝ] F) (A B : E →L[ℝ] E) :
    dist (trace b H A) (trace b G B)≤(Fintype.card ι:ℝ)*(‖H-G‖*‖A‖+‖G‖*‖A-B‖) := by
  have he : trace b H A-trace b G B=trace b (H-G) A+trace b G (A-B) := by
    rw [sub_left,sub_right]; abel
  rw [dist_eq_norm,he]
  exact (norm_add_le _ _).trans ((add_le_add (norm_bound b (H-G) A) (norm_bound b G (A-B))).trans_eq (by ring))

lemma holder_error (b : OrthonormalBasis ι ℝ E) (H : E → E →L[ℝ] E →L[ℝ] F)
    (A : E → E →L[ℝ] E) (A0 : E →L[ℝ] E) {a S B M e : ℝ}
    (hS : 0≤S) (hB : 0≤B) (_hM : 0≤M) (_he : 0≤e)
    (hH : ∀ x y,dist (H x) (H y)≤S*dist x y^a) (hHb : ∀ x,‖H x‖≤B)
    (hA : ∀ x y,dist (A x) (A y)≤M*dist x y^a) (hAb : ∀ x,‖A0-A x‖≤e) :
    ∀ x y,dist (trace b (H x) (A0-A x)) (trace b (H y) (A0-A y))≤
      ((Fintype.card ι:ℝ)*(e*S+M*B))*dist x y^a := by
  intro x y
  have hp := Real.rpow_nonneg (dist_nonneg : 0≤dist x y) a
  have ht := variation b (H x) (H y) (A0-A x) (A0-A y)
  have heq : A0-A x-(A0-A y)= -(A x-A y) := by abel
  rw [heq,norm_neg] at ht
  have hHxy := hH x y
  rw [dist_eq_norm (H x) (H y)] at hHxy
  have hAxy := hA x y
  rw [dist_eq_norm (A x) (A y)] at hAxy
  have h1 := mul_le_mul hHxy (hAb x)
    (norm_nonneg _) (mul_nonneg hS hp)
  have h2 := mul_le_mul (hHb y) hAxy
    (norm_nonneg _) hB
  exact ht.trans ((mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg _)).trans_eq (by ring))
end CoefficientTrace
end
namespace HolderAbsorption
open Filter Metric
open scoped Topology
variable {X : Type*} {Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem improve {f : X → Y} {a K S : ℝ} (hK : 0≤K) (hS : 0≤S)
    (hinit : ∀ x y,dist (f x) (f y)≤S*dist x y^a)
    (hstep : ∀ s : ℝ, 0 ≤ s → (∀ x y,dist (f x) (f y)≤ s*dist x y^a) →
      ∀ x y,dist (f x) (f y)≤(K+s/2)*dist x y^a) :
    ∀ x y,dist (f x) (f y)≤(2*K)*dist x y^a := by
  have hb (n : ℕ) : ∀ x y,dist (f x) (f y)≤(2*K+S*(1/2:ℝ)^n)*dist x y^a := by
    induction n with
    | zero =>
      intro x y
      apply (hinit x y).trans
      have hp := Real.rpow_nonneg (dist_nonneg : 0≤dist x y) a
      norm_num only [pow_zero,mul_one]
      nlinarith
    | succ n ih =>
      have hh := hstep (2*K+S*(1/2:ℝ)^n) (by positivity) ih
      intro x y
      convert hh x y using 1; ring
  intro x y
  have ht : Tendsto (fun n : ℕ => (2*K+S*(1/2:ℝ)^n)*dist x y^a) atTop
      (𝓝 ((2*K)*dist x y^a)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
    convert (tendsto_const_nhds.add (tendsto_const_nhds.mul hp)).mul_const (dist x y^a) using 1; simp
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Filter.Eventually.of_forall fun n => hb n x y)
end HolderAbsorption
noncomputable section
namespace CompactMollification
open Set MeasureTheory Metric Filter
open scoped SchwartzMap Topology InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma elliptic_trace (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    {u : E → ℂ} (hu : ContDiff ℝ 2 u) (x : E) :
    elliptic b A u x=CoefficientTrace.trace b (HessianInterpolation.hessian u x) A := by
  simp only [elliptic,CoefficientTrace.trace,dd_hessian hu]

theorem variable_schauder (b : OrthonormalBasis ι ℝ E) (A0 : E →L[ℝ] E)
    (hA0 : ∀ x:E,x≠0 → 0<⟪x,A0 x⟫_ℝ) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ e : ℝ,0<e ∧ ∀ M B0 C : ℝ,0≤M → 0≤B0 → 0≤C →
      ∃ U : ℝ,0≤U ∧ ∀ (u : E → ℂ) (A : E → E →L[ℝ] E),
        HasCompactSupport u → ContDiff ℝ 2 u →
        (∀ x,‖u x‖≤B0) → (∀ x,‖A0-A x‖≤e) →
        (∀ x y,dist (A x) (A y)≤M*dist x y^a) →
        (∀ x y,dist (CoefficientTrace.trace b (HessianInterpolation.hessian u x) (A x))
          (CoefficientTrace.trace b (HessianInterpolation.hessian u y) (A y))≤C*dist x y^a) →
        (∃ S : ℝ,0≤S ∧ ∀ x y,dist (HessianInterpolation.hessian u x)
          (HessianInterpolation.hessian u y)≤S*dist x y^a) →
        ∀ x y,dist (HessianInterpolation.hessian u x) (HessianInterpolation.hessian u y)≤U*dist x y^a := by
  obtain ⟨T,hT,hSchauder⟩ := hessian_schauder b A0 hA0 ha ha1
  let n : ℝ := Fintype.card ι
  have hn : 0≤n := Nat.cast_nonneg _
  let e : ℝ := 1/(4*T*n+1)
  have he : 0<e := by dsimp only [e]; positivity
  have hesmall : T*n*e≤1/4 := by
    dsimp only [e]
    have hd : 0<4*T*n+1 := by positivity
    rw [← mul_div_assoc,div_le_iff₀ hd]
    nlinarith
  refine ⟨e,he,?_⟩
  intro M B0 C hM hB0 hC
  let k : ℝ := T*(1+n*M)
  have hk : 0<k := by dsimp only [k]; positivity
  let d : ℝ := 1/(16*k+1)
  have hd : 0<d := by dsimp only [d]; positivity
  let r : ℝ := d^(1/a)/2
  have hr : 0<r := by dsimp only [r]; positivity
  have hrpow : (2*r)^a=d := by
    have heq : 2*r=d^(1/a) := by dsimp only [r]; ring
    rw [heq,← Real.rpow_mul hd.le]
    rw [one_div_mul_cancel ha.ne',Real.rpow_one]
  have hrsmall : 4*k*(2*r)^a≤1/4 := by
    rw [hrpow]
    dsimp only [d]
    have hden : 0<16*k+1 := by positivity
    rw [← mul_div_assoc,div_le_iff₀ hden]
    nlinarith
  let b0 : ℝ := 2*B0/r^2
  let K : ℝ := T*((1+n*M)*b0+C)
  have hb0 : 0≤b0 := by dsimp only [b0]; positivity
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨2*K,by positivity,?_⟩
  intro u A hc hu hBound hAb hA hP hFinite
  obtain ⟨S,hS,hHolder⟩ := hFinite
  apply HolderAbsorption.improve hK hS hHolder
  intro s hs hHs
  let B : ℝ := b0+4*s*(2*r)^a
  have hB : 0≤B := by dsimp only [B]; positivity
  have hHb (x : E) : ‖HessianInterpolation.hessian u x‖≤B :=
    HessianInterpolation.norm_bound hu hB0 hs ha.le hr hBound hHs x
  have hError := CoefficientTrace.holder_error b (HessianInterpolation.hessian u) A A0
    hs hB hM he.le hHs hHb hA hAb
  have hFrozen (x y : E) : dist (elliptic b A0 u x) (elliptic b A0 u y)≤
      (C+n*(e*s+M*B))*dist x y^a := by
    have heq (z : E) : elliptic b A0 u z=
        CoefficientTrace.trace b (HessianInterpolation.hessian u z) (A z)+
        CoefficientTrace.trace b (HessianInterpolation.hessian u z) (A0-A z) := by
      rw [elliptic_trace b A0 hu,CoefficientTrace.sub_right]
      abel
    rw [heq x,heq y]
    exact (dist_add_add_le _ _ _ _).trans ((add_le_add (hP x y) (hError x y)).trans_eq (by ring))
  have hHS := hSchauder u hc hu (C+n*(e*s+M*B)) B (by positivity) hB hHb hFrozen
  have hsmall : T*(B+(C+n*(e*s+M*B)))≤K+s/2 := by
    have heq : T*(B+(C+n*(e*s+M*B)))=K+(4*k*(2*r)^a+T*n*e)*s := by
      dsimp only [B,K,k]
      ring
    rw [heq]
    have hh : 4*k*(2*r)^a+T*n*e≤1/2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hh hs]
  intro x y
  exact (hHS x y).trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg dist_nonneg _))
end CompactMollification

namespace HessianInterpolation
open Set Metric
open scoped ContDiff
variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma hessian_comp (L : F →L[ℝ] G) {u : E → F} (hu : ContDiff ℝ 2 u) (x : E) :
    hessian (fun z => L (u z)) x=(ContinuousLinearMap.compL ℝ E F G L).comp (hessian u x) := by
  have hd := hu.differentiable (by norm_num : (2:WithTop ℕ∞)≠0)
  have hd2 := (hu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable one_ne_zero
  have heq : fderiv ℝ (fun z => L (u z))=(fun z => L.comp (fderiv ℝ u z)) := by
    funext z
    exact (L.hasFDerivAt.comp z (hd z).hasFDerivAt).fderiv
  dsimp only [hessian]
  rw [heq]
  exact ((ContinuousLinearMap.compL ℝ E F G L).hasFDerivAt.comp x (hd2 x).hasFDerivAt).fderiv

lemma complexLift_apply (H : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    complexLift H v w=(H v w:ℂ) := rfl
lemma complexLift_sub (H G : E →L[ℝ] E →L[ℝ] ℝ) :
    complexLift (H-G)=complexLift H-complexLift G := by
  ext v w
  simp only [complexLift_apply,sub_apply,Complex.ofReal_sub]
lemma complexLift_norm (H : E →L[ℝ] E →L[ℝ] ℝ) : ‖complexLift H‖=‖H‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (f := complexLift H) (norm_nonneg H)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound (f := (complexLift H) v) (by positivity)
    intro w
    rw [complexLift_apply,Complex.norm_real]
    have h1 := (H v).le_opNorm w
    have h2 := H.le_opNorm v
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
  · apply ContinuousLinearMap.opNorm_le_bound (f := H) (norm_nonneg (complexLift H))
    intro v
    apply ContinuousLinearMap.opNorm_le_bound (f := H v) (by positivity)
    intro w
    have h1 := ((complexLift H) v).le_opNorm w
    have h2 := (complexLift H).le_opNorm v
    rw [complexLift_apply,Complex.norm_real] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
lemma complexLift_dist (H G : E →L[ℝ] E →L[ℝ] ℝ) : dist (complexLift H) (complexLift G)=dist H G := by
  rw [dist_eq_norm (complexLift H) (complexLift G),← complexLift_sub,complexLift_norm,dist_eq_norm H G]
lemma hessian_complex {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    hessian (fun z => (u z:ℂ)) x=complexLift (hessian u x) := hessian_comp Complex.ofRealCLM hu x
end HessianInterpolation

namespace CompactMollification
open Set MeasureTheory Metric Filter
open scoped SchwartzMap Topology InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma trace_complex (b : OrthonormalBasis ι ℝ E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (A : E →L[ℝ] E) :
    CoefficientTrace.trace b (HessianInterpolation.complexLift H) A=Complex.ofReal (CoefficientTrace.trace b H A) := by
  simp only [CoefficientTrace.trace,HessianInterpolation.complexLift_apply,Complex.ofReal_sum]

theorem real_variable_schauder (b : OrthonormalBasis ι ℝ E) (A0 : E →L[ℝ] E)
    (hA0 : ∀ x:E,x≠0 → 0<⟪x,A0 x⟫_ℝ) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ e : ℝ,0<e ∧ ∀ M B0 C : ℝ,0≤M → 0≤B0 → 0≤C →
      ∃ U : ℝ,0≤U ∧ ∀ (u : E → ℝ) (A : E → E →L[ℝ] E),
        HasCompactSupport u → ContDiff ℝ 2 u →
        (∀ x,‖u x‖≤B0) → (∀ x,‖A0-A x‖≤e) →
        (∀ x y,dist (A x) (A y)≤M*dist x y^a) →
        (∀ x y,dist (CoefficientTrace.trace b (HessianInterpolation.hessian u x) (A x))
          (CoefficientTrace.trace b (HessianInterpolation.hessian u y) (A y))≤C*dist x y^a) →
        (∃ S : ℝ,0≤S ∧ ∀ x y,dist (HessianInterpolation.hessian u x)
          (HessianInterpolation.hessian u y)≤S*dist x y^a) →
        ∀ x y,dist (HessianInterpolation.hessian u x) (HessianInterpolation.hessian u y)≤U*dist x y^a := by
  obtain ⟨e,he,hrest⟩ := variable_schauder b A0 hA0 ha ha1
  refine ⟨e,he,?_⟩
  intro M B0 C hM hB0 hC
  obtain ⟨U,hU,hbound⟩ := hrest M B0 C hM hB0 hC
  refine ⟨U,hU,?_⟩
  intro u A hc hu hb hAb hA hP hFinite
  let uc : E → ℂ := fun x => (u x:ℂ)
  have huc : ContDiff ℝ 2 uc := Complex.ofRealCLM.contDiff.comp hu
  have hcc : HasCompactSupport uc := hc.comp_left (g := fun r : ℝ => (r:ℂ)) (by simp)
  have hbc (x : E) : ‖uc x‖≤B0 := by simpa only [uc,Complex.norm_real] using hb x
  have hPc (x y : E) : dist (CoefficientTrace.trace b (HessianInterpolation.hessian uc x) (A x))
      (CoefficientTrace.trace b (HessianInterpolation.hessian uc y) (A y))≤C*dist x y^a := by
    rw [HessianInterpolation.hessian_complex hu,HessianInterpolation.hessian_complex hu,trace_complex,trace_complex]
    simpa only [Complex.isometry_ofReal.dist_eq] using hP x y
  obtain ⟨S,hS,hHs⟩ := hFinite
  have hFinitec : ∃ S : ℝ,0≤S ∧ ∀ x y,dist (HessianInterpolation.hessian uc x)
      (HessianInterpolation.hessian uc y)≤S*dist x y^a := by
    refine ⟨S,hS,?_⟩
    intro x y
    rw [HessianInterpolation.hessian_complex hu,HessianInterpolation.hessian_complex hu,HessianInterpolation.complexLift_dist]
    exact hHs x y
  intro x y
  have hh := hbound uc A hcc huc hbc hAb hA hPc hFinitec x y
  rwa [HessianInterpolation.hessian_complex hu,HessianInterpolation.hessian_complex hu,HessianInterpolation.complexLift_dist] at hh
end CompactMollification

namespace HolderLocalization
open Set Metric
variable {E : Type*} {F : Type*} {G : Type*} {H : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ F] in
lemma of_lipschitz_bounded {f : E → F} {L B a : ℝ} (hL : 0≤L) (hB : 0≤B)
    (ha : 0≤a) (ha1 : a≤1) (hf : ∀ x y,dist (f x) (f y)≤L*dist x y)
    (hb : ∀ x,‖f x‖≤B) : ∀ x y,dist (f x) (f y)≤(L+2*B)*dist x y^a := by
  intro x y
  by_cases hd : dist x y≤1
  · have hp : dist x y≤dist x y^a := by
      by_cases hz : dist x y=0
      · rw [hz]; positivity
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne dist_nonneg (Ne.symm hz)) hd ha1
    exact (hf x y).trans ((mul_le_mul_of_nonneg_left hp hL).trans
      (mul_le_mul_of_nonneg_right (by linarith : L≤L+2*B) (Real.rpow_nonneg dist_nonneg a)))
  · have hp : 1≤dist x y^a := Real.one_le_rpow (le_of_not_ge hd) ha
    have hm : dist (f x) (f y)≤2*B := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hb x,hb y])
    calc
      _ ≤ 2*B := hm
      _ ≤ (L+2*B)*dist x y^a := by nlinarith

lemma bilinear_holder (T : F →L[ℝ] G →L[ℝ] H) {s : Set E} {f : E → F} {g : E → G}
    {B D C K a : ℝ} (hB : 0≤B) (_hD : 0≤D) (hC : 0≤C)
    (hfb : ∀ x∈s,‖f x‖≤B) (hgb : ∀ x∈s,‖g x‖≤D)
    (hfc : ∀ x∈s,∀ y∈s,dist (f x) (f y)≤C*dist x y^a)
    (hgc : ∀ x∈s,∀ y∈s,dist (g x) (g y)≤K*dist x y^a) :
    ∀ x∈s,∀ y∈s,dist (T (f x) (g x)) (T (f y) (g y))≤‖T‖*(B*K+D*C)*dist x y^a := by
  intro x hx y hy
  have he : T (f x) (g x)-T (f y) (g y)=T (f x) (g x-g y)+T (f x-f y) (g y) := by
    simp only [map_sub,sub_apply]
    abel
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖T (f x) (g x-g y)‖+‖T (f x-f y) (g y)‖ := norm_add_le _ _
    _ ≤ ‖T‖*B*(K*dist x y^a)+‖T‖*(C*dist x y^a)*D := by
      apply add_le_add
      · exact (T.le_opNorm₂ _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hfb x hx) (norm_nonneg T))
          (by simpa only [dist_eq_norm] using hgc x hx y hy) (norm_nonneg _) (by positivity))
      · exact (T.le_opNorm₂ _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hfc x hx y hy) (norm_nonneg T))
          (hgb y hy) (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma localized_bilinear (T : F →L[ℝ] G →L[ℝ] H) {s : Set E} {f : E → F} {g : E → G}
    {B D C K a : ℝ} (hB : 0≤B) (hD : 0≤D) (hC : 0≤C) (hK : 0≤K)
    (hfb : ∀ x,‖f x‖≤B) (hfz : ∀ x,x∉s → f x=0)
    (hgb : ∀ x∈s,‖g x‖≤D)
    (hfc : ∀ x y,dist (f x) (f y)≤C*dist x y^a)
    (hgc : ∀ x∈s,∀ y∈s,dist (g x) (g y)≤K*dist x y^a) :
    (∀ x,‖T (f x) (g x)‖≤‖T‖*B*D) ∧
    ∀ x y,dist (T (f x) (g x)) (T (f y) (g y))≤‖T‖*(B*K+D*C)*dist x y^a := by
  have hb (x : E) : ‖T (f x) (g x)‖≤‖T‖*B*D := by
    by_cases hx : x∈s
    · exact (T.le_opNorm₂ _ _).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (hfb x) (norm_nonneg T)) (hgb x hx) (norm_nonneg _) (by positivity))
    · simp only [hfz x hx,map_zero,zero_apply,norm_zero]
      positivity
  refine ⟨hb,?_⟩
  have hmain (x : E) (hx : x∈s) (y : E) :
      dist (T (f x) (g x)) (T (f y) (g y))≤‖T‖*(B*K+D*C)*dist x y^a := by
    by_cases hy : y∈s
    · exact bilinear_holder T hB hD hC (fun z _ => hfb z) hgb
        (fun z _ w _ => hfc z w) hgc x hx y hy
    · rw [hfz y hy,map_zero,zero_apply,dist_zero_right]
      have hf : ‖f x‖≤C*dist x y^a := by simpa only [hfz y hy,dist_zero_right] using hfc x y
      have hp := Real.rpow_nonneg (dist_nonneg : 0≤dist x y) a
      calc
        _ ≤ ‖T‖*(C*dist x y^a)*D := (T.le_opNorm₂ _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left hf (norm_nonneg T)) (hgb x hx) (norm_nonneg _) (by positivity))
        _ ≤ ‖T‖*(B*K+D*C)*dist x y^a := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg T) (mul_nonneg hB hK)) hp]
  intro x y
  by_cases hx : x∈s
  · exact hmain x hx y
  by_cases hy : y∈s
  · simpa only [dist_comm] using hmain y hy x
  · simp only [hfz x hx,hfz y hy,map_zero,zero_apply,dist_self]
    positivity
end HolderLocalization
namespace HolderControl
section
open Set Metric
variable {E : Type*} {F : Type*} {G : Type*} {H : Type*} {J : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ F] in
lemma Controlled.add {a : ℝ} {s : Set E} {f g : J → E → F}
    (hf : Controlled a s f) (hg : Controlled a s g) :
    Controlled a s (fun j x => f j x+g j x) := by
  obtain ⟨B,C,hB,hC,hfb,hfc⟩ := hf
  obtain ⟨D,K,hD,hK,hgb,hgc⟩ := hg
  refine ⟨B+D,C+K,by positivity,by positivity,?_,?_⟩
  · intro j x hx
    exact (norm_add_le _ _).trans (add_le_add (hfb j x hx) (hgb j x hx))
  · intro j x hx y hy
    exact (dist_add_add_le _ _ _ _).trans ((add_le_add (hfc j x hx y hy) (hgc j x hx y hy)).trans_eq (by ring))

lemma Controlled.localized_bilinear (T : F →L[ℝ] G →L[ℝ] H) {a : ℝ} {s : Set E}
    {f : J → E → F} {g : J → E → G}
    (hf : Controlled a univ f) (hfz : ∀ j x,x∉s → f j x=0)
    (hg : Controlled a s g) : Controlled a univ (fun j x => T (f j x) (g j x)) := by
  obtain ⟨B,C,hB,hC,hfb,hfc⟩ := hf
  obtain ⟨D,K,hD,hK,hgb,hgc⟩ := hg
  refine ⟨‖T‖*B*D,‖T‖*(B*K+D*C),by positivity,by positivity,?_,?_⟩
  · intro j x _
    exact (HolderLocalization.localized_bilinear T hB hD hC hK (fun x => hfb j x (mem_univ x))
      (hfz j) (hgb j) (fun x y => hfc j x (mem_univ x) y (mem_univ y)) (hgc j)).1 x
  · intro j x _ y _
    exact (HolderLocalization.localized_bilinear T hB hD hC hK (fun x => hfb j x (mem_univ x))
      (hfz j) (hgb j) (fun x y => hfc j x (mem_univ x) y (mem_univ y)) (hgc j)).2 x y

omit [NormedSpace ℝ F] in
lemma Controlled.of_single {a : ℝ} {s : Set E} {f : E → F}
    (hf : Controlled a s (fun _ : Unit => f)) : Controlled a s (fun _ : J => f) := by
  obtain ⟨B,C,hB,hC,hfb,hfc⟩ := hf
  exact ⟨B,C,hB,hC,fun _ => hfb (),fun _ => hfc ()⟩

omit [NormedSpace ℝ F] in
lemma Controlled.congr {a : ℝ} {s : Set E} {f g : J → E → F}
    (hf : Controlled a s f) (he : ∀ j x,x∈s → f j x=g j x) : Controlled a s g := by
  obtain ⟨B,C,hB,hC,hfb,hfc⟩ := hf
  exact ⟨B,C,hB,hC,fun j x hx => he j x hx ▸ hfb j x hx,
    fun j x hx y hy => by rw [← he j x hx,← he j y hy]; exact hfc j x hx y hy⟩

end

open Set Metric
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_C1 {a : ℝ} (ha : 0≤a) (ha1 : a≤1) {f : E → F}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Controlled a univ (fun _ : Unit => f) := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨D,hD⟩ := hc.fderiv (𝕜:=ℝ) |>.exists_bound_of_continuous (contDiff_one_iff_fderiv.mp hf).2
  have hB0 : 0≤B := (norm_nonneg (f 0)).trans (hB 0)
  have hD0 : 0≤D := (norm_nonneg (fderiv ℝ f 0)).trans (hD 0)
  have hl : LipschitzWith ⟨D,hD0⟩ f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable one_ne_zero) (fun x => hD x)
  refine ⟨B,D+2*B,hB0,by positivity,fun _ x _ => hB x,?_⟩
  intro _ x _ y _
  exact HolderLocalization.of_lipschitz_bounded hD0 hB0 ha ha1 hl.dist_le_mul hB x y
end HolderControl

namespace HessianInterpolation
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hessian_mul {χ u : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : E) :
    hessian (fun z => χ z*u z) x=χ x • hessian u x+
      (u x • hessian χ x+(fderiv ℝ χ x).smulRight (fderiv ℝ u x)+
        (fderiv ℝ u x).smulRight (fderiv ℝ χ x)) := by
  have hdχ := (hχ.differentiable (by norm_num : (2:ℕ∞ω)≠0))
  have hdu := (hu.differentiable (by norm_num : (2:ℕ∞ω)≠0))
  have hDχ := ((hχ.fderiv_right (m:=1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt
  have hDu := ((hu.fderiv_right (m:=1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt
  have hh := ((hdχ x).hasFDerivAt.smul hDu).add ((hdu x).hasFDerivAt.smul hDχ)
  have heq : (fun z => χ z • fderiv ℝ u z+u z • fderiv ℝ χ z)=
      fderiv ℝ (fun z => χ z*u z) := funext fun z => (fderiv_fun_mul (hdχ z) (hdu z)).symm
  change HasFDerivAt (fun z => χ z • fderiv ℝ u z+u z • fderiv ℝ χ z) _ x at hh
  rw [heq] at hh
  unfold hessian
  rw [hh.fderiv]
  abel
end HessianInterpolation

namespace HolderControl
section
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} {F : Type*} {J : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

lemma Controlled.trace (b : OrthonormalBasis ι ℝ E) {a : ℝ} {s : Set E}
    {H : J → E → E →L[ℝ] E →L[ℝ] F} {A : J → E → E →L[ℝ] E}
    (hH : Controlled a s H) (hA : Controlled a s A) :
    Controlled a s (fun j x => CoefficientTrace.trace b (H j x) (A j x)) := by
  obtain ⟨B,C,hB,hC,hHb,hHc⟩ := hH
  obtain ⟨D,K,hD,hK,hAb,hAc⟩ := hA
  refine ⟨(Fintype.card ι:ℝ)*B*D,(Fintype.card ι:ℝ)*(C*D+B*K),by positivity,by positivity,?_,?_⟩
  · intro j x hx
    exact (CoefficientTrace.norm_bound b _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hHb j x hx) (Nat.cast_nonneg _)) (hAb j x hx) (norm_nonneg _) (by positivity))
  · intro j x hx y hy
    have hHxy : ‖H j x-H j y‖≤C*dist x y^a := by simpa only [dist_eq_norm] using hHc j x hx y hy
    have hAxy : ‖A j x-A j y‖≤K*dist x y^a := by simpa only [dist_eq_norm] using hAc j x hx y hy
    refine (CoefficientTrace.variation b _ _ _ _).trans ?_
    have h1 := mul_le_mul hHxy (hAb j x hx) (norm_nonneg _) (by positivity : 0≤C*dist x y^a)
    have h2 := mul_le_mul (hHb j y hy) hAxy (norm_nonneg _) hB
    exact (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg _)).trans_eq (by ring)
end

section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
variable {E : Type*} {J : Type*} {J' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma Controlled.reindex {F : Type*} [NormedAddCommGroup F] {a : ℝ} {s : Set E}
    {f : J → E → F} (hf : Controlled a s f) (i : J' → J) :
    Controlled a s (fun j => f (i j)) := by
  obtain ⟨B,C,hB,hC,hfb,hfc⟩ := hf
  exact ⟨B,C,hB,hC,fun j => hfb (i j),fun j => hfc (i j)⟩

attribute [local instance] OAI.HolderControl.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.HolderControl.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.HolderControl.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.HolderControl.instNormedSpaceRealContinuousLinearMapId_solutions_1
theorem localized_family (b : OrthonormalBasis ι ℝ E) (A0 : E →L[ℝ] E)
    (hA0 : ∀ x:E,x≠0 → 0<⟪x,A0 x⟫_ℝ) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ e : ℝ,0<e ∧ ∀ (u : J → E → ℝ) (A : J → E → E →L[ℝ] E)
      (χ : E → ℝ) (s t : Set E),
      ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ⊆s →
      IsOpen t → (∀ x∈t,χ x=1) → (∀ j,ContDiff ℝ 2 (u j)) →
      (∀ j x,‖A0-A j x‖≤e) → Controlled a univ A →
      Controlled a s u → Controlled a s (fun j => fderiv ℝ (u j)) →
      Controlled a s (fun j x => CoefficientTrace.trace b (HessianInterpolation.hessian (u j) x) (A j x)) →
      (∀ j,Controlled a s (fun _ : Unit => HessianInterpolation.hessian (u j))) →
      Controlled a t (fun j => HessianInterpolation.hessian (u j)) := by
  obtain ⟨e,he,hsch⟩ := CompactMollification.real_variable_schauder b A0 hA0 ha ha1
  refine ⟨e,he,?_⟩
  intro u A χ s t hχ hc hs ht htχ hu hclose hA hub hDu hP hFinite
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by decide)
  have hχc : Controlled a univ (fun _ : J => χ) :=
    (compact_C1 ha.le ha1.le (hχ.of_le (by simp)) hc).of_single
  have hDχ : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hD2χ : ContDiff ℝ ∞ (HessianInterpolation.hessian χ) := hDχ.fderiv_right (by simp)
  have hDχc : Controlled a univ (fun _ : J => fderiv ℝ χ) :=
    (compact_C1 ha.le ha1.le (hDχ.of_le (by simp)) (hc.fderiv ℝ)).of_single
  have hD2χc : Controlled a univ (fun _ : J => HessianInterpolation.hessian χ) :=
    (compact_C1 ha.le ha1.le (hD2χ.of_le (by simp)) ((hc.fderiv ℝ).fderiv ℝ)).of_single
  have hz (x : E) (hx : x∉s) : χ x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
  have hDz (x : E) (hx : x∉s) : fderiv ℝ χ x=0 :=
    fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs hh))
  have hD2z (x : E) (hx : x∉s) : HessianInterpolation.hessian χ x=0 :=
    fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs (tsupport_fderiv_subset ℝ hh)))
  let w : J → E → ℝ := fun j x => χ x*u j x
  let R : J → E → E →L[ℝ] E →L[ℝ] ℝ := fun j x =>
    u j x • HessianInterpolation.hessian χ x+(fderiv ℝ χ x).smulRight (fderiv ℝ (u j) x)+
      (fderiv ℝ (u j) x).smulRight (fderiv ℝ χ x)
  have hwc : Controlled a univ w :=
    hχc.localized_bilinear (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ => hz) hub
  have hR : Controlled a univ R := by
    have h1 := hD2χc.localized_bilinear (ContinuousLinearMap.lsmul ℝ ℝ).flip (fun _ => hD2z) hub
    have h2 := hDχc.localized_bilinear (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (fun _ => hDz) hDu
    have h3 := hDχc.localized_bilinear (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).flip (fun _ => hDz) hDu
    exact (h1.add h2).add h3
  have hprod (j : J) (x : E) : HessianInterpolation.hessian (w j) x=
      χ x • HessianInterpolation.hessian (u j) x+R j x :=
    HessianInterpolation.hessian_mul hχ2 (hu j) x
  have hPw : Controlled a univ (fun j x => CoefficientTrace.trace b (HessianInterpolation.hessian (w j) x) (A j x)) := by
    have h1 := hχc.localized_bilinear (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ => hz) hP
    have h2 := hR.trace b hA
    apply (h1.add h2).congr
    intro j x _
    change χ x*CoefficientTrace.trace b (HessianInterpolation.hessian (u j) x) (A j x)+
      CoefficientTrace.trace b (R j x) (A j x)=_
    rw [hprod]
    simp only [CoefficientTrace.trace,add_apply,_root_.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_add_distrib]
  have hwFinite (j : J) : Controlled a univ (fun _ : Unit => HessianInterpolation.hessian (w j)) := by
    have h1 := (hχc.reindex (fun _ : Unit => j)).localized_bilinear (ContinuousLinearMap.lsmul ℝ ℝ)
      (fun _ => hz) (hFinite j)
    exact (h1.add (hR.reindex (fun _ : Unit => j))).congr (fun _ x _ => (hprod j x).symm)
  obtain ⟨B,C,hB,hC,hwb,_⟩ := hwc
  obtain ⟨D,M,hD,hM,_,hAc⟩ := hA
  obtain ⟨P,N,hP0,hN,_,hPwc⟩ := hPw
  obtain ⟨U,hU,hUniform⟩ := hsch M B N hM hB hN
  have hw2 (j : J) : ContDiff ℝ 2 (w j) := hχ2.mul (hu j)
  have hwH (j : J) : ∀ x y,dist (HessianInterpolation.hessian (w j) x)
      (HessianInterpolation.hessian (w j) y)≤U*dist x y^a := by
    obtain ⟨Bj,S,hBj,hS,_,hSj⟩ := hwFinite j
    exact hUniform (w j) (A j) hc.mul_right (hw2 j)
      (fun x => hwb j x (mem_univ x)) (hclose j)
      (fun x y => hAc j x (mem_univ x) y (mem_univ y))
      (fun x y => hPwc j x (mem_univ x) y (mem_univ y))
      ⟨S,hS,fun x y => hSj () x (mem_univ x) y (mem_univ y)⟩
  have heq (j : J) (x : E) (hx : x∈t) :
      HessianInterpolation.hessian (w j) x=HessianInterpolation.hessian (u j) x := by
    have hev : w j =ᶠ[𝓝 x] u j := by
      filter_upwards [ht.eventually_mem hx] with y hy
      simp only [w,htχ y hy,one_mul]
    exact hev.fderiv.fderiv_eq
  refine ⟨2*B+4*U*2^a,U,by positivity,hU,?_,?_⟩
  · intro j x hx
    change ‖HessianInterpolation.hessian (u j) x‖≤_
    rw [← heq j x hx]
    have hh := HessianInterpolation.norm_bound (hw2 j) hB hU ha.le (by norm_num : (0:ℝ)<1)
      (fun x => hwb j x (mem_univ x)) (hwH j) x
    simpa using hh
  · intro j x hx y hy
    change dist (HessianInterpolation.hessian (u j) x) (HessianInterpolation.hessian (u j) y)≤_
    rw [← heq j x hx,← heq j y hy]
    exact hwH j x y
end

section
open Set Metric
variable {E : Type*} {F : Type*} {G : Type*} {H : Type*} {J : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ F] in
lemma Controlled.mono {a:ℝ} {s t:Set E} {f:J→E→F} (hf:Controlled a s f) (ht:t⊆s) :
    Controlled a t f := by
  obtain ⟨B,C,hB,hC,hb,hc⟩ := hf
  exact ⟨B,C,hB,hC,fun j x hx => hb j x (ht hx),fun j x hx y hy => hc j x (ht hx) y (ht hy)⟩

omit [NormedSpace ℝ F] in
lemma const (a:ℝ) (s:Set E) (v:F) : Controlled a s (fun _:J => fun _:E => v) := by
  exact ⟨‖v‖,0,norm_nonneg _,le_rfl,fun _ _ _ => le_rfl,by simp⟩

omit [NormedSpace ℝ F] in
lemma Controlled.sub {a:ℝ} {s:Set E} {f g:J→E→F} (hf:Controlled a s f)
    (hg:Controlled a s g) : Controlled a s (fun j x => f j x-g j x) := by
  obtain ⟨B,C,hB,hC,hb,hc⟩ := hf
  obtain ⟨D,K,hD,hK,hd,hk⟩ := hg
  refine ⟨B+D,C+K,by positivity,by positivity,?_,?_⟩
  · intro j x hx
    exact (norm_sub_le _ _).trans (add_le_add (hb j x hx) (hd j x hx))
  · intro j x hx y hy
    exact (dist_sub_sub_le _ _ _ _).trans ((add_le_add (hc j x hx y hy) (hk j x hx y hy)).trans_eq (by ring))

lemma Controlled.linear (T:F→L[ℝ]G) {a:ℝ} {s:Set E} {f:J→E→F}
    (hf:Controlled a s f) : Controlled a s (fun j x => T (f j x)) := by
  obtain ⟨B,C,hB,hC,hb,hc⟩ := hf
  refine ⟨‖T‖*B,‖T‖*C,by positivity,by positivity,?_,?_⟩
  · intro j x hx
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb j x hx) (norm_nonneg _))
  · intro j x hx y hy
    rw [dist_eq_norm,← map_sub]
    exact (T.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using hc j x hx y hy) (norm_nonneg T)).trans_eq (by ring))

lemma Controlled.bilinear (T:F→L[ℝ]G→L[ℝ]H) {a:ℝ} {s:Set E} {f:J→E→F} {g:J→E→G}
    (hf:Controlled a s f) (hg:Controlled a s g) : Controlled a s (fun j x => T (f j x) (g j x)) := by
  obtain ⟨B,C,hB,hC,hb,hc⟩ := hf
  obtain ⟨D,K,hD,hK,hd,hk⟩ := hg
  refine ⟨‖T‖*B*D,‖T‖*(B*K+D*C),by positivity,by positivity,?_,?_⟩
  · intro j x hx
    exact (T.le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left
      (hb j x hx) (norm_nonneg T)) (hd j x hx) (norm_nonneg _) (by positivity))
  · intro j x hx y hy
    exact HolderLocalization.bilinear_holder T hB hD hC (hb j) (hd j) (hc j) (hk j) x hx y hy

end

section
open Set Metric
variable {E : Type*} {F : Type*} {J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma extend_field {a e:ℝ} (ha:0≤a) (ha1:a≤1) (he:0≤e)
    (A0:F) (A:J→E→F) (ψ:E→ℝ) (s t:Set E)
    (hψ:ContDiff ℝ 1 ψ) (hc:HasCompactSupport ψ) (hz:∀x,x∉s → ψ x=0)
    (hb:∀x,‖ψ x‖≤1) (h1:∀x∈t,ψ x=1)
    (hA:Controlled a s A) (hclose:∀ j x,x∈s → ‖A0-A j x‖≤e) :
    ∃ B:J→E→F,Controlled a univ B ∧ (∀j x,‖A0-B j x‖≤e) ∧
      ∀j x,x∈t → B j x=A j x := by
  let B:J→E→F := fun j x => A0+ψ x • (A j x-A0)
  have hpc : Controlled a univ (fun _:J => ψ) := (compact_C1 ha ha1 hψ hc).of_single
  have hAc := hA.sub (const a s A0)
  have hBc : Controlled a univ B := (const a univ A0).add
    (hpc.localized_bilinear (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ => hz) hAc)
  refine ⟨B,hBc,?_,?_⟩
  · intro j x
    by_cases hx:x∈s
    · have heq : A0-B j x= -(ψ x • (A j x-A0)) := by dsimp only [B]; abel
      rw [heq,norm_neg,norm_smul]
      have hdist : ‖A j x-A0‖≤e := by rw [norm_sub_rev]; exact hclose j x hx
      exact (mul_le_mul (hb x) hdist (norm_nonneg _) zero_le_one).trans_eq (one_mul e)
    · simpa only [B,hz x hx,zero_smul,add_zero,sub_self,norm_zero] using he
  · intro j x hx
    simp only [B,h1 x hx,one_smul,add_sub_cancel]
end

section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
variable {E : Type*} {J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

theorem interior_family (b : OrthonormalBasis ι ℝ E) (A0 : E →L[ℝ] E)
    (hA0 : ∀ x:E,x≠0 → 0<⟪x,A0 x⟫_ℝ) {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ e : ℝ,0<e ∧ ∀ (u : J → E → ℝ) (A : J → E → E →L[ℝ] E)
      (ψ χ : E → ℝ) (s s₀ t : Set E),
      ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ⊆s₀ →
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → (∀x,x∉s → ψ x=0) →
      (∀x,‖ψ x‖≤1) → (∀x∈s₀,ψ x=1) → s₀⊆s →
      IsOpen t → (∀ x∈t,χ x=1) → (∀ j,ContDiff ℝ 2 (u j)) →
      (∀ j x,x∈s → ‖A0-A j x‖≤e) → Controlled a s A →
      Controlled a s u → Controlled a s (fun j => fderiv ℝ (u j)) →
      Controlled a s (fun j x => CoefficientTrace.trace b (HessianInterpolation.hessian (u j) x) (A j x)) →
      (∀ j,Controlled a s (fun _ : Unit => HessianInterpolation.hessian (u j))) →
      Controlled a t (fun j => HessianInterpolation.hessian (u j)) := by
  obtain ⟨e,he,hsch⟩ := localized_family (J:=J) b A0 hA0 ha ha1
  refine ⟨e,he,?_⟩
  intro u A ψ χ s s₀ t hχ hc hcs hψ hpc hpz hpb hp1 hs ht h1 hu hclose hA hub hDu hP hF
  obtain ⟨B,hB,hBc,hBe⟩ := extend_field ha.le ha1.le he.le A0 A ψ s s₀ hψ hpc hpz hpb hp1 hA hclose
  apply hsch u B χ s₀ t hχ hc hcs ht h1 hu hBc hB (hub.mono hs) (hDu.mono hs)
  · exact (hP.mono hs).congr (fun j x hx => by rw [hBe j x hx])
  · exact fun j => (hF j).mono hs
end

open Set Metric
open scoped ContDiff InnerProductSpace
variable {E : Type*} {J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι:Type*} [Fintype ι]

theorem interior_ball (b:OrthonormalBasis ι ℝ E) (A0:E→L[ℝ]E)
    (hA0:∀x:E,x≠0 → 0<⟪x,A0 x⟫_ℝ) {a:ℝ} (ha:0<a) (ha1:a<1) :
    ∃e:ℝ,0<e ∧ ∀(c:E) (r:ℝ),0<r → ∀(u:J→E→ℝ) (A:J→E→E→L[ℝ]E),
      (∀j,ContDiff ℝ 2 (u j)) → (∀j x,x∈ball c r → ‖A0-A j x‖≤e) →
      Controlled a (ball c r) A → Controlled a (ball c r) u →
      Controlled a (ball c r) (fun j => fderiv ℝ (u j)) →
      Controlled a (ball c r) (fun j x => CoefficientTrace.trace b (HessianInterpolation.hessian (u j) x) (A j x)) →
      (∀j,Controlled a (ball c r) (fun _:Unit => HessianInterpolation.hessian (u j))) →
      Controlled a (ball c (r/4)) (fun j => HessianInterpolation.hessian (u j)) := by
  obtain ⟨e,he,hs⟩ := interior_family (J:=J) b A0 hA0 ha ha1
  refine ⟨e,he,?_⟩
  intro c r hr u A hu hc hA hU hDu hP hF
  let ψ:ContDiffBump c := ⟨r/2,3*r/4,by positivity,by linarith⟩
  let χ:ContDiffBump c := ⟨r/4,r/3,by positivity,by linarith⟩
  apply hs u A ψ χ (ball c r) (ball c (r/2)) (ball c (r/4)) χ.contDiff χ.hasCompactSupport
  · rw [χ.tsupport_eq]
    intro x hx
    exact mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by dsimp only [χ]; linarith))
  · exact ψ.contDiff
  · exact ψ.hasCompactSupport
  · intro x hx
    exact ψ.zero_of_le_dist (by dsimp only [ψ]; have hh:=not_lt.mp (mt mem_ball.mpr hx); linarith)
  · intro x
    rw [Real.norm_eq_abs,abs_of_nonneg ψ.nonneg]
    exact ψ.le_one
  · intro x hx
    exact ψ.one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hx).le)
  · exact ball_subset_ball (by linarith)
  · exact isOpen_ball
  · intro x hx
    exact χ.one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hx).le)
  · exact hu
  · exact hc
  · exact hA
  · exact hU
  · exact hDu
  · exact hP
  · exact hF
end HolderControl
end


noncomputable section
namespace HessianTrace
section
open Matrix InnerProductSpace
open scoped InnerProductSpace ContDiff Matrix.Norms.Elementwise
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma scalar_hessian {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x v w : E) :
    HessianInterpolation.hessian u x v w=⟪fderiv ℝ (gradient u) x v,w⟫_ℝ := by
  have hg : ContDiff ℝ 1 (gradient u) :=
    (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp (hu.fderiv_right (by norm_num))
  have h := (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    ((hg.differentiable one_ne_zero x).hasFDerivAt)
  change HasFDerivAt ((toDual ℝ E) ∘ gradient u)
    ((toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x)) x at h
  rw [toDual_comp_gradient] at h
  have he := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) h.fderiv
  exact he

lemma trace_eq_matrix {u : E → ℝ} (hu : ContDiff ℝ 2 u) (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (x : E) :
    CoefficientTrace.trace b (HessianInterpolation.hessian u x) A=
      (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap *
        LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient u) x).toLinearMap).trace := by
  rw [← LinearMap.toMatrix_mul,← LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  rw [LinearMap.trace_mul_comm,LinearMap.trace_eq_sum_inner _ b]
  unfold CoefficientTrace.trace
  apply Finset.sum_congr rfl
  intro i _
  rw [show HessianInterpolation.hessian u x (b i) (A (b i))=
      HessianInterpolation.hessian u x (A (b i)) (b i) from
        hu.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _]
  rw [scalar_hessian hu]
  exact real_inner_comm _ _

end


open Matrix Set InnerProductSpace
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

local instance instTopologicalSpaceMatrixReal_solutions_1_rd4c0af_1 : TopologicalSpace (Matrix ι ι ℝ) :=
  (inferInstance : PseudoMetricSpace (Matrix ι ι ℝ)).toUniformSpace.toTopologicalSpace
lemma toMatrix_fromMatrix (b:OrthonormalBasis ι ℝ E) (M:Matrix ι ι ℝ) :
    LinearMap.toMatrix b.toBasis b.toBasis (fromMatrix b M).toLinearMap=M := by
  change (LinearMap.toMatrix b.toBasis b.toBasis) ((LinearMap.toMatrix b.toBasis b.toBasis).symm M)=M
  exact LinearEquiv.apply_symm_apply _ _

lemma inner_pos_fromMatrix (b:OrthonormalBasis ι ℝ E) {M:Matrix ι ι ℝ} (hM:M.PosDef)
    (v:E) (hv:v≠0) : 0<⟪v,fromMatrix b M v⟫_ℝ := by
  have hcoord:(b.toBasis.repr v:ι→ℝ)≠0 := by
    intro he
    have hz:b.toBasis.repr v=0 := DFunLike.coe_injective he
    exact hv (b.toBasis.repr.injective (by simpa using hz))
  have hh := hM.dotProduct_mulVec_pos hcoord
  rw [← toMatrix_fromMatrix b M,LinearMap.toMatrix_mulVec_repr] at hh
  have he (w:E) : (b.toBasis.repr w:ι→ℝ)=WithLp.ofLp (b.repr w) := by
    ext i
    exact b.coe_toBasis_repr_apply w i
  rw [he v] at hh
  change 0<star (b.repr v).ofLp ⬝ᵥ (b.toBasis.repr (fromMatrix b M v):ι→ℝ) at hh
  rw [he (fromMatrix b M v)] at hh
  have hi := b.repr.inner_map_map v (fromMatrix b M v)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simp only [star_trivial] at hh hi
  rw [dotProduct_comm] at hi
  rwa [hi] at hh
end HessianTrace


namespace HolderControl
open Set Metric
variable {E : Type*} {F : Type*} {J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_convex_C1 {a:ℝ} (ha:0≤a) (ha1:a≤1) {K:Set E} (hK:IsCompact K)
    (hconv:Convex ℝ K) {f:E→F} (hf:ContDiff ℝ 1 f) :
    Controlled a K (fun _:J => f) := by
  obtain ⟨B,hB⟩ := (hK.image hf.continuous).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (hK.image (contDiff_one_iff_fderiv.mp hf).2).isBounded.exists_norm_le
  let B₀ := max B 0
  let D₀ := max D 0
  have hB₀ : 0≤B₀ := le_max_right _ _
  have hD₀ : 0≤D₀ := le_max_right _ _
  have hb (x:E) (hx:x∈K) : ‖f x‖≤B₀ := (hB _ (mem_image_of_mem f hx)).trans (le_max_left _ _)
  have hd (x:E) (hx:x∈K) : ‖fderiv ℝ f x‖≤D₀ := (hD _ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hl : LipschitzOnWith ⟨D₀,hD₀⟩ f K :=
    hconv.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hf.differentiable one_ne_zero x)
      (fun x hx => hd x hx)
  have hls : ∀x y:K,dist (f x) (f y)≤D₀*dist x y := fun x y => hl.dist_le_mul x x.prop y y.prop
  refine ⟨B₀,D₀+2*B₀,hB₀,by positivity,fun _ => hb,?_⟩
  intro _ x hx y hy
  exact HolderLocalization.of_lipschitz_bounded hD₀ hB₀ ha ha1 hls (fun x:K => hb x x.prop) ⟨x,hx⟩ ⟨y,hy⟩
end HolderControl


namespace FiniteDifference
section
open Set Metric MeasureTheory
open scoped ContDiff
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma hasDerivAt_ray {g : E → F} (hg : ContDiff ℝ 1 g) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (x+s • v)) (fderiv ℝ g (x+t • v) v) t := by
  have hr : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa only [id_eq,one_smul] using (((hasDerivAt_id t).smul_const v).const_add x)
  exact ((hg.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt t hr

omit [CompleteSpace F] in
lemma ray_integrable {g : E → F} (hg : ContDiff ℝ 1 g) (x v : E) :
    IntervalIntegrable (fun t : ℝ => fderiv ℝ g (x+t • v) v) volume (0:ℝ) 1 := by
  have hc : Continuous (fderiv ℝ g) := (contDiff_one_iff_fderiv.mp hg).2
  exact ((hc.comp (show Continuous (fun t : ℝ => x+t • v) by fun_prop)).clm_apply continuous_const).intervalIntegrable 0 1

lemma increment_integral {g : E → F} (hg : ContDiff ℝ 1 g) (x v : E) :
    increment g v x=∫ t in (0:ℝ)..1,fderiv ℝ g (x+t • v) v := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=1) (fun t _ => hasDerivAt_ray hg x v t) (ray_integrable hg x v)
  simpa only [one_smul,zero_smul,add_zero,increment] using h.symm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
lemma ray_mem {Ω : Set E} (hΩ : Convex ℝ Ω) {x v : E} (hx : x∈Ω) (hxv : x+v∈Ω)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : x+t • v∈Ω := by
  have hh := hΩ hx hxv (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  convert hh using 1
  module

lemma increment_holder {g : E → F} (hg : ContDiff ℝ 1 g) {Ω : Set E}
    (hΩ : Convex ℝ Ω) {C a : ℝ} (_hC : 0≤C)
    (hH : ∀ x∈Ω,∀ y∈Ω,dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*dist x y^a)
    {x y v : E} (hx : x∈Ω) (hy : y∈Ω) (hxv : x+v∈Ω) (hyv : y+v∈Ω) :
    dist (increment g v x) (increment g v y)≤C*‖v‖*dist x y^a := by
  rw [dist_eq_norm,increment_integral hg,increment_integral hg,← intervalIntegral.integral_sub
    (ray_integrable hg x v) (ray_integrable hg y v)]
  have hb (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      ‖fderiv ℝ g (x+t • v) v-fderiv ℝ g (y+t • v) v‖≤C*‖v‖*dist x y^a := by
    have hh := hH _ (ray_mem hΩ hx hxv ht) _ (ray_mem hΩ hy hyv ht)
    rw [dist_add_right,dist_eq_norm] at hh
    calc
      _ ≤ ‖fderiv ℝ g (x+t • v)-fderiv ℝ g (y+t • v)‖*‖v‖ :=
        (fderiv ℝ g (x+t • v)-fderiv ℝ g (y+t • v)).le_opNorm v
      _ ≤ (C*dist x y^a)*‖v‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ = _ := by ring
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
    (fun t ht => hb t ⟨(by simpa using ht.1.le),(by simpa using ht.2)⟩)
  simpa using hh

lemma increment_bound {g : E → F} (hg : ContDiff ℝ 1 g) {Ω : Set E}
    (hΩ : Convex ℝ Ω) {B : ℝ} (hH : ∀ x∈Ω,‖fderiv ℝ g x‖≤B)
    {x v : E} (hx : x∈Ω) (hxv : x+v∈Ω) : ‖increment g v x‖≤B*‖v‖ := by
  rw [increment_integral hg]
  have hb (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ‖fderiv ℝ g (x+t • v) v‖≤B*‖v‖ :=
    ((fderiv ℝ g (x+t • v)).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (hH _ (ray_mem hΩ hx hxv ht)) (norm_nonneg _))
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
    (fun t ht => hb t ⟨(by simpa using ht.1.le),(by simpa using ht.2)⟩)
  simpa using hh
end


open Set Metric
variable {E : Type*} {F : Type*} {J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma normalized_controlled {a : ℝ} {Ω s : Set E} (hΩ : Convex ℝ Ω)
    {g : E → F} (hg : ContDiff ℝ 1 g)
    (hD : HolderControl.Controlled a Ω (fun _ : Unit => fderiv ℝ g))
    (v : J → E) (hs : s⊆Ω) (hshift : ∀ j x,x∈s → x+v j∈Ω) :
    HolderControl.Controlled a s (fun j => normalized g (v j)) := by
  obtain ⟨B,C,hB,hC,hDb,hDc⟩ := hD
  refine ⟨B,C,hB,hC,?_,?_⟩
  · intro j x hx
    change ‖normalized g (v j) x‖≤B
    by_cases hv : v j=0
    · simp only [normalized,hv,norm_zero,inv_zero,zero_smul]; exact hB
    have hn : 0<‖v j‖ := norm_pos_iff.mpr hv
    rw [normalized,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    have hh := increment_bound hg hΩ (hDb ()) (hs hx) (hshift j x hx)
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans_eq (by field_simp)
  · intro j x hx y hy
    change dist (normalized g (v j) x) (normalized g (v j) y)≤C*dist x y^a
    by_cases hv : v j=0
    · simp only [normalized,hv,norm_zero,inv_zero,zero_smul,dist_self]; positivity
    have hn : 0<‖v j‖ := norm_pos_iff.mpr hv
    rw [normalized,normalized,dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    have hh := increment_holder hg hΩ hC (hDc ()) (hs hx) (hs hy) (hshift j x hx) (hshift j y hy)
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans_eq (by field_simp)

omit [CompleteSpace F] in
lemma fderiv_normalized {g : E → F} (hg : ContDiff ℝ 1 g) (v x : E) :
    fderiv ℝ (normalized g v) x=normalized (fderiv ℝ g) v x := by
  have hd := hg.differentiable one_ne_zero
  unfold normalized increment
  rw [fderiv_fun_const_smul (f := fun y => g (y+v)-g y)
    (((hd (x+v)).comp x (differentiableAt_id.add_const v)).sub (hd x)),
    fderiv_fun_sub (f := fun y => g (y+v)) (g :=g)
      ((hd (x+v)).comp x (differentiableAt_id.add_const v)) (hd x),fderiv_comp_add_right]
end FiniteDifference


namespace MomentQuotient
section
open Matrix Set InnerProductSpace
open scoped ContDiff Matrix.Norms.Elementwise InnerProductSpace
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
lemma quotient_contDiff {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v : E) :
    ContDiff ℝ 2 (quotient u v) :=
  contDiff_const.mul ((hu.comp (contDiff_id.add contDiff_const)).sub hu)

omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
lemma hessian_quotient {u : E → ℝ} (hu : ContDiff ℝ 2 u) (v x : E) :
    HessianInterpolation.hessian (quotient u v) x=
      ‖v‖⁻¹ • (HessianInterpolation.hessian u (x+v)-HessianInterpolation.hessian u x) := by
  have hd := hu.differentiable (by norm_num : (2:ℕ∞ω)≠0)
  have hD := (hu.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiable one_ne_zero
  have hq : fderiv ℝ (quotient u v)=fun y => ‖v‖⁻¹ • (fderiv ℝ u (y+v)-fderiv ℝ u y) := by
    funext y
    change fderiv ℝ (fun y => ‖v‖⁻¹ • (u (y+v)-u y)) y=_
    rw [fderiv_fun_const_smul (f := fun y => u (y+v)-u y) (((hd (y+v)).comp y (differentiableAt_id.add_const v)).sub (hd y)),
      fderiv_fun_sub (f := fun y => u (y+v)) (g := u) ((hd (y+v)).comp y (differentiableAt_id.add_const v)) (hd y),fderiv_comp_add_right]
  unfold HessianInterpolation.hessian
  rw [hq,fderiv_fun_const_smul (f := fun y => fderiv ℝ u (y+v)-fderiv ℝ u y) (((hD (x+v)).comp x (differentiableAt_id.add_const v)).sub (hD x)),
    fderiv_fun_sub (f := fun y => fderiv ℝ u (y+v)) (g := fderiv ℝ u) ((hD (x+v)).comp x (differentiableAt_id.add_const v)) (hD x),fderiv_comp_add_right]

end


open Set Metric InnerProductSpace
open scoped ContDiff
variable {E : Type*} {J : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.MomentQuotient.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.MomentQuotient.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.MomentQuotient.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.MomentQuotient.instNormedSpaceRealContinuousLinearMapId_solutions_1
omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
lemma normalized_hessian_finite {u:E→ℝ} (hu:ContDiff ℝ 2 u) {a:ℝ} {K s:Set E}
    (hH:HolderControl.Controlled a K (fun _:Unit => HessianInterpolation.hessian u))
    (hs:s⊆K) (v:E) (hshift:∀x∈s,x+v∈K) :
    HolderControl.Controlled a s (fun _:Unit => HessianInterpolation.hessian (quotient u v)) := by
  obtain ⟨B,C,hB,hC,hb,hc⟩ := hH
  have hshiftC:HolderControl.Controlled a s (fun _:Unit => fun x => HessianInterpolation.hessian u (x+v)) := by
    refine ⟨B,C,hB,hC,fun _ x hx => hb () (x+v) (hshift x hx),?_⟩
    intro _ x hx y hy
    simpa only [dist_add_right] using hc () (x+v) (hshift x hx) (y+v) (hshift y hy)
  have hbase:HolderControl.Controlled a s (fun _:Unit => HessianInterpolation.hessian u) :=
    (show HolderControl.Controlled a K (fun _:Unit => HessianInterpolation.hessian u) from
      ⟨B,C,hB,hC,hb,hc⟩).mono hs
  have hdiff := (hshiftC.sub hbase).linear ((ContinuousLinearMap.lsmul ℝ ℝ) ‖v‖⁻¹)
  exact hdiff.congr (fun _ x _ => (hessian_quotient hu v x).symm)

end MomentQuotient



namespace AEDerivativeLocal
open Filter Set Metric MeasureTheory
open scoped Topology NNReal
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
lemma increment_bound {g : E → F} {Ω : Set E} {L : ℝ≥0} (hg : LipschitzOnWith L g Ω)
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (A : E →L[ℝ] F) {e : ℝ}
    (_he : 0≤e) (ha : ∀ᵐ z ∂μ,z∈Ω → DifferentiableAt ℝ g z ∧ ‖fderiv ℝ g z-A‖≤e)
    {x h : E} (hx : x∈Ω) (hxh : x+h∈Ω) :
    ‖g (x+h)-g x-A h‖≤e*‖h‖ := by
  obtain ⟨ω,hω,hωv⟩ := exists_dual_vector'' ℝ (g (x+h)-g x-A h)
  let f : E → ℝ := fun z => ω (g z-A z)
  have hf : LipschitzOnWith (‖ω‖₊*(L+‖A‖₊)) f Ω :=
    ω.lipschitz.comp_lipschitzOnWith (hg.sub A.lipschitz.lipschitzOnWith)
  obtain ⟨fbar,hfbar,heq⟩ := hf.extend_real
  have hevent {z : E} (hz : z∈Ω) : fbar=ᶠ[𝓝 z] f :=
    Filter.Eventually.mono (hΩ.mem_nhds hz) (fun y hy => (heq hy).symm)
  have ha' : ∀ᵐ z ∂μ,z∈Ω → DifferentiableAt ℝ fbar z ∧ fderiv ℝ fbar z h≤e*‖h‖ := by
    filter_upwards [ha] with z hz hzΩ
    have hdg := (hz hzΩ).1.hasFDerivAt.sub A.hasFDerivAt
    have hd := (ω.hasFDerivAt.comp z hdg).congr_of_eventuallyEq (hevent hzΩ)
    refine ⟨hd.differentiableAt,?_⟩
    rw [hd.fderiv]
    change ω ((fderiv ℝ g z-A) h)≤_
    have hh := (ContinuousLinearMap.le_opNorm (fderiv ℝ g z-A) h).trans
      (mul_le_mul_of_nonneg_right (hz hzΩ).2 (norm_nonneg h))
    calc
      _ ≤ ‖ω ((fderiv ℝ g z-A) h)‖ := le_abs_self _
      _ ≤ ‖ω‖*‖(fderiv ℝ g z-A) h‖ := ω.le_opNorm _
      _ ≤ 1*(e*‖h‖) := mul_le_mul hω hh (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hh := AESlice.difference_le_ae μ hfbar hΩ hc ha' (a:=1) (by norm_num) hx
    (by simpa only [one_smul] using hxh)
  simp only [one_smul,mul_one] at hh
  rw [← heq hx,← heq hxh] at hh
  have hid : f (x+h)-f x=ω (g (x+h)-g x-A h) := by
    dsimp only [f]
    rw [← map_sub,map_add]
    congr 1
    abel
  rwa [hid,hωv] at hh

theorem hasFDerivAt_of_ae {g : E → F} {Ω : Set E} {L : ℝ≥0}
    (hg : LipschitzOnWith L g Ω) (hΩ : IsOpen Ω)
    {A : E → E →L[ℝ] F} (hA : ContinuousOn A Ω)
    (ha : ∀ᵐ z ∂μ,z∈Ω → HasFDerivAt g (A z) z) {x : E} (hx : x∈Ω) :
    HasFDerivAt g (A x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro e he
  have hAc : ContinuousAt A x := (hA x hx).continuousAt (hΩ.mem_nhds hx)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    ((hAc.eventually (Metric.ball_mem_nhds (A x) he)).and (hΩ.mem_nhds hx))
  have hs : ball x r⊆Ω := fun z hz => (hball (mem_ball.mp hz)).2
  have ha' : ∀ᵐ z ∂μ,z∈ball x r → DifferentiableAt ℝ g z ∧ ‖fderiv ℝ g z-A x‖≤e := by
    filter_upwards [ha] with z hz hzB
    refine ⟨(hz (hs hzB)).differentiableAt,?_⟩
    rw [(hz (hs hzB)).fderiv]
    exact le_of_lt (by simpa only [mem_ball,dist_eq_norm] using (hball (mem_ball.mp hzB)).1)
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hhB
  exact increment_bound μ (hg.mono hs) isOpen_ball (convex_ball _ _) (A x) he.le ha'
    (mem_ball_self hr) (by simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hhB)
end AEDerivativeLocal

namespace QuotientBootstrap
open Set Filter Metric MeasureTheory
open scoped Topology NNReal
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
lemma derivative_holder {g : E → F} {Ω : Set E} (hΩ : IsOpen Ω) {a U : ℝ}
    (hU : 0≤U)
    (hQ : ∀ x∈Ω,∀ y∈Ω,∀ v:E,x+v∈Ω → y+v∈Ω →
      ‖g (x+v)-g x-(g (y+v)-g y)‖≤U*‖v‖*dist x y^a)
    {x y : E} (hx : x∈Ω) (hy : y∈Ω)
    (hdx : DifferentiableAt ℝ g x) (hdy : DifferentiableAt ℝ g y) :
    dist (fderiv ℝ g x) (fderiv ℝ g y)≤U*dist x y^a := by
  rw [dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound (f:=fderiv ℝ g x-fderiv ℝ g y) (by positivity)
  intro v
  have hxlim := (hdx.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
  have hylim := (hdy.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
  have hlim := (hxlim.sub hylim).norm
  have hxev : ∀ᶠ t:ℝ in 𝓝[>] 0,x+t • v∈Ω := by
    have ht : Tendsto (fun t:ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul,add_zero] using
        ((show Continuous (fun t:ℝ => x+t • v) from by fun_prop).tendsto (0:ℝ))
    exact (ht.eventually (hΩ.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
  have hyev : ∀ᶠ t:ℝ in 𝓝[>] 0,y+t • v∈Ω := by
    have ht : Tendsto (fun t:ℝ => y+t • v) (𝓝 0) (𝓝 y) := by
      simpa only [zero_smul,add_zero] using
        ((show Continuous (fun t:ℝ => y+t • v) from by fun_prop).tendsto (0:ℝ))
    exact (ht.eventually (hΩ.mem_nhds hy)).filter_mono nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [hxev,hyev,self_mem_nhdsWithin] with t hxt hyt ht
  have ht0 : 0<t := ht
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht0]
  have hh := mul_le_mul_of_nonneg_left (hQ x hx y hy (t • v) hxt hyt) (inv_nonneg.mpr ht0.le)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht0] at hh
  convert hh using 1
  field_simp

theorem contDiffOn_one_of_quotients (μ : Measure E) [μ.IsAddHaarMeasure]
    {g : E → F} {Ω : Set E} {L : ℝ≥0} (hg : LipschitzOnWith L g Ω)
    (hΩ : IsOpen Ω) {a U : ℝ} (ha : 0<a) (hU : 0≤U)
    (hQ : ∀ x∈Ω,∀ y∈Ω,∀ v:E,x+v∈Ω → y+v∈Ω →
      ‖g (x+v)-g x-(g (y+v)-g y)‖≤U*‖v‖*dist x y^a) :
    ContDiffOn ℝ 1 g Ω ∧ ∀ x∈Ω,∀ y∈Ω,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤U*dist x y^a := by
  classical
  have hae : ∀ᵐ z ∂μ,z∈Ω → DifferentiableAt ℝ g z := by
    filter_upwards [hg.ae_differentiableWithinAt_of_mem (μ:=μ)] with z hz hzΩ
    exact (hz hzΩ).differentiableAt (hΩ.mem_nhds hzΩ)
  let G : Set Ω := {z | DifferentiableAt ℝ g z}
  have hG : Dense G := by
    have hd : Dense ((Subtype.val : Ω → E) ⁻¹' {z | z∈Ω → DifferentiableAt ℝ g z}) :=
      (Measure.dense_of_ae hae).preimage hΩ.isOpenMap_subtype_val
    have he : ((Subtype.val : Ω → E) ⁻¹' {z | z∈Ω → DifferentiableAt ℝ g z})=G := by
      ext z
      exact ⟨fun hz => hz z.prop,fun hz _ => hz⟩
    rwa [he] at hd
  let H : Ω → E →L[ℝ] F := fun z => fderiv ℝ g z
  have hGH (x : Ω) (hx : x∈G) (y : Ω) (hy : y∈G) :
      dist (H x) (H y)≤U*dist x y^a :=
    derivative_holder hΩ hU hQ x.prop y.prop hx hy
  have hp : Continuous (fun p : Ω×Ω => U*dist p.1 p.2^a) :=
    continuous_const.mul ((continuous_fst.dist continuous_snd).rpow_const (fun _ => Or.inr ha.le))
  obtain ⟨A,hAc,hArep⟩ := ContinuousEnvelope.exists_continuous_extension hG H (by
    intro c e he
    have hz : U*dist c c^a<e := by simpa only [dist_self,Real.zero_rpow ha.ne',mul_zero] using he
    obtain ⟨r,hr,hb⟩ := Metric.eventually_nhds_iff.mp
      ((hp.continuousAt (x := (c,c))).eventually (isOpen_Iio.mem_nhds hz))
    refine ⟨r,hr,?_⟩
    intro x hx hxc y hy hyc
    exact (hGH x hx y hy).trans_lt (hb (y := (x,y)) (by simpa only [Prod.dist_eq] using max_lt hxc hyc)))
  let Abar : E → E →L[ℝ] F := fun z => if hz:z∈Ω then A ⟨z,hz⟩ else 0
  have hAbar (z : Ω) : Abar z=A z := by simp only [Abar,dite_eq_left z.prop]
  have hAcbar : ContinuousOn Abar Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z:Ω => Abar z)
    simpa only [hAbar] using hAc
  have haA : ∀ᵐ z ∂μ,z∈Ω → HasFDerivAt g (Abar z) z := by
    filter_upwards [hae] with z hz hzΩ
    rw [show Abar z=A ⟨z,hzΩ⟩ from hAbar ⟨z,hzΩ⟩,hArep ⟨z,hzΩ⟩ (hz hzΩ)]
    exact (hz hzΩ).hasFDerivAt
  have hd (z : E) (hz : z∈Ω) := AEDerivativeLocal.hasFDerivAt_of_ae μ hg hΩ hAcbar haA hz
  have hc : ContDiffOn ℝ 1 g Ω := by
    change ContDiffOn ℝ (0+1) g Ω
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mpr
    refine ⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt,(by simp),?_⟩
    rw [contDiffOn_zero]
    exact hAcbar.congr (fun z hz => (hd z hz).fderiv)
  refine ⟨hc,?_⟩
  intro x hx y hy
  exact derivative_holder hΩ hU hQ hx hy (hd x hx).differentiableAt (hd y hy).differentiableAt
end QuotientBootstrap


namespace FiniteDifference
open Set Metric MeasureTheory
open scoped ContDiff NNReal
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem C1_of_controlled_normalized (μ : Measure E) [μ.IsAddHaarMeasure]
    {g : E → F} {c : E} {r a : ℝ} (_hr : 0<r) (ha : 0<a)
    (hQ : HolderControl.Controlled a (ball c r)
      (fun v : {v:E // ‖v‖<2*r} => normalized g v.val)) :
    ContDiffOn ℝ 1 g (ball c r) ∧ ∃ U:ℝ,0≤U ∧ ∀ x∈ball c r,∀ y∈ball c r,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤U*dist x y^a := by
  obtain ⟨B,U,hB,hU,hb,hc⟩ := hQ
  have hsmall {x y:E} (hx:x∈ball c r) (hy:y∈ball c r) : ‖y-x‖<2*r := by
    rw [← dist_eq_norm]
    exact (dist_triangle y c x).trans_lt (by rw [dist_comm c x]; linarith [mem_ball.mp hy,mem_ball.mp hx])
  have hnorm (v x:E) : g (x+v)-g x=‖v‖ • normalized g v x := by
    by_cases hv:v=0
    · simp [hv,normalized,increment]
    · simp only [normalized,increment,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  have hLip : LipschitzOnWith ⟨B,hB⟩ g (ball c r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hh := hb ⟨y-x,hsmall hx hy⟩ x hx
    have he : x+(y-x)=y := by abel
    change dist (g x) (g y)≤B*dist x y
    rw [dist_comm (g x)]
    conv_lhs => rw [dist_eq_norm]
    calc
      ‖g y-g x‖=‖y-x‖*‖normalized g (y-x) x‖ := by
        conv_lhs => rw [← he,hnorm]
        rw [norm_smul,Real.norm_eq_abs,abs_norm]
      _ ≤ ‖y-x‖*B := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = B*dist x y := by rw [← dist_eq_norm,dist_comm y x,mul_comm]
  have hinc : ∀ x∈ball c r,∀ y∈ball c r,∀ v:E,x+v∈ball c r → y+v∈ball c r →
      ‖g (x+v)-g x-(g (y+v)-g y)‖≤U*‖v‖*dist x y^a := by
    intro x hx y hy v hxv _
    have hv : ‖v‖<2*r := by simpa only [add_sub_cancel_left] using hsmall hx hxv
    have hh := hc ⟨v,hv⟩ x hx y hy
    rw [hnorm v x,hnorm v y,← smul_sub,norm_smul,Real.norm_eq_abs,abs_norm]
    exact (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hh)
      (norm_nonneg v)).trans_eq (by rw [← dist_eq_norm]; ring)
  obtain ⟨h1,h2⟩ := QuotientBootstrap.contDiffOn_one_of_quotients μ hLip isOpen_ball ha hU hinc
  exact ⟨h1,U,hU,h2⟩
end FiniteDifference


namespace LinearSchauder
open Set Metric InnerProductSpace MomentQuotient
open scoped ContDiff InnerProductSpace
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.LinearSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.LinearSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
lemma quotient_equation (b:OrthonormalBasis ι ℝ E) {u S:E→ℝ} {A:E→E→L[ℝ]E}
    (hu:ContDiff ℝ 2 u) (heq:∀x,CoefficientTrace.trace b (HessianInterpolation.hessian u x) (A x)=S x)
    (v x:E) :
    CoefficientTrace.trace b (HessianInterpolation.hessian (quotient u v) x) (A x)=
      FiniteDifference.normalized S v x-CoefficientTrace.trace b (HessianInterpolation.hessian u (x+v))
        (FiniteDifference.normalized A v x) := by
  rw [hessian_quotient hu]
  change CoefficientTrace.bilinear b (‖v‖⁻¹ • (_-_)) (A x)=_
  rw [map_smul,map_sub]
  change ‖v‖⁻¹*(CoefficientTrace.trace b (HessianInterpolation.hessian u (x+v)) (A x)-
    CoefficientTrace.trace b (HessianInterpolation.hessian u x) (A x))=_
  rw [heq]
  unfold FiniteDifference.normalized FiniteDifference.increment
  change _=‖v‖⁻¹*(S (x+v)-S x)-CoefficientTrace.bilinear b
    (HessianInterpolation.hessian u (x+v)) (‖v‖⁻¹ • (A (x+v)-A x))
  rw [map_smul,map_sub]
  change _=‖v‖⁻¹*(S (x+v)-S x)-‖v‖⁻¹*
    (CoefficientTrace.trace b (HessianInterpolation.hessian u (x+v)) (A (x+v))-
      CoefficientTrace.trace b (HessianInterpolation.hessian u (x+v)) (A x))
  rw [heq]
  ring

attribute [local instance] OAI.LinearSchauder.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.LinearSchauder.instNormedSpaceRealContinuousLinearMapId_solutions_1
omit [DecidableEq ι] in

theorem C3_local (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (b:OrthonormalBasis ι ℝ E) {u S:E→ℝ} {A:E→E→L[ℝ]E}
    (hu:ContDiff ℝ 2 u) (hA:ContDiff ℝ 1 A) (hS:ContDiff ℝ 1 S)
    (heq:∀x,CoefficientTrace.trace b (HessianInterpolation.hessian u x) (A x)=S x)
    {c:E} (hp:∀x:E,x≠0 → 0<⟪x,A c x⟫_ℝ) {R a:ℝ} (hR:0<R) (ha:0<a) (ha1:a<1)
    (hH:HolderControl.Controlled a (closedBall c R) (fun _:Unit => HessianInterpolation.hessian u))
    (hDA:HolderControl.Controlled a (closedBall c R) (fun _:Unit => fderiv ℝ A))
    (hDS:HolderControl.Controlled a (closedBall c R) (fun _:Unit => fderiv ℝ S)) :
    ∃r:ℝ,0<r ∧ ContDiffOn ℝ 3 u (ball c r) ∧
      ∃U:ℝ,0≤U ∧ ∀x∈ball c r,∀y∈ball c r,
        dist (fderiv ℝ (HessianInterpolation.hessian u) x)
          (fderiv ℝ (HessianInterpolation.hessian u) y)≤U*dist x y^a := by
  obtain ⟨e,he,hs⟩ := HolderControl.interior_ball (J:={v:E // ‖v‖<1}) b (A c) hp ha ha1
  obtain ⟨d,hd,hnear⟩ := Metric.continuousAt_iff.mp (hA.continuous.continuousAt (x:=c)) e he
  let r:ℝ:=min R d/4
  have hr:0<r := div_pos (lt_min hR hd) (by norm_num)
  have hrR:r≤R/4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hrd:r≤d/4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let v:{v:E // ‖v‖<1}→E := fun w=>r • w.val
  have hv (w:{v:E // ‖v‖<1}) : ‖v w‖<r := by
    dsimp only [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith [w.prop]
  have hKr : ball c r⊆closedBall c R := by
    intro x hx
    exact mem_closedBall.mpr (by linarith [mem_ball.mp hx])
  have hshift (w:{v:E // ‖v‖<1}) (x:E) (hx:x∈ball c r) : x+v w∈closedBall c R := by
    have hb := dist_triangle (x+v w) x c
    rw [dist_eq_norm (x+v w) x,add_sub_cancel_left] at hb
    exact mem_closedBall.mpr (by linarith [mem_ball.mp hx,hv w])
  have hDuc := HolderControl.compact_convex_C1 (J:=Unit) ha.le ha1.le
    (isCompact_closedBall c R) (convex_closedBall c R)
    (hu.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2))
  have hQ := FiniteDifference.normalized_controlled (convex_closedBall c R)
    (hu.of_le (by norm_num : (1:ℕ∞ω)≤2)) hDuc v hKr hshift
  have hDQ := FiniteDifference.normalized_controlled (convex_closedBall c R)
    (hu.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)) hH v hKr hshift
  have hSQ := FiniteDifference.normalized_controlled (convex_closedBall c R) hS hDS v hKr hshift
  have hAQ := FiniteDifference.normalized_controlled (convex_closedBall c R) hA hDA v hKr hshift
  have hHshift:HolderControl.Controlled a (ball c r)
      (fun w x => HessianInterpolation.hessian u (x+v w)) := by
    obtain ⟨B,C,hB,hC,hb,hc⟩ := hH
    refine ⟨B,C,hB,hC,fun w x hx => hb () (x+v w) (hshift w x hx),?_⟩
    intro w x hx y hy
    simpa only [dist_add_right] using hc () (x+v w) (hshift w x hx) (y+v w) (hshift w y hy)
  have hP := hSQ.sub (hHshift.bilinear (CoefficientTrace.bilinear b) hAQ)
  have hAc := HolderControl.compact_convex_C1 (J:=Unit) ha.le ha1.le
    (isCompact_closedBall c R) (convex_closedBall c R) hA
  have hQr := hs c r hr (fun w => quotient u (v w)) (fun _ x => A x)
    (fun w => quotient_contDiff hu (v w)) (fun _ x hx => by
      rw [← dist_eq_norm,dist_comm]
      exact (hnear (by linarith [mem_ball.mp hx])).le)
    (hAc.mono hKr).of_single
    (hQ.congr (fun _ _ _ => rfl))
    (hDQ.congr (fun w x _ => (FiniteDifference.fderiv_normalized
      (hu.of_le (by norm_num : (1:ℕ∞ω)≤2)) (v w) x).symm))
    (hP.congr (fun w x _ => (quotient_equation b hu heq (v w) x).symm))
    (fun w => normalized_hessian_finite hu hH hKr (v w) (hshift w))
  have hsmall (w:{w:E // ‖w‖<2*(r/4)}) : ‖r⁻¹ • w.val‖<1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    apply (inv_mul_lt_iff₀ hr).2
    nlinarith [w.prop]
  have hnorm:HolderControl.Controlled a (ball c (r/4))
      (fun w:{w:E // ‖w‖<2*(r/4)} => FiniteDifference.normalized (HessianInterpolation.hessian u) w.val) := by
    have hh := hQr.reindex (fun w:{w:E // ‖w‖<2*(r/4)} => ⟨r⁻¹ • w.val,hsmall w⟩)
    apply hh.congr
    intro w x _
    rw [hessian_quotient hu]
    simp only [v,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    rfl
  obtain ⟨hC1,U,hU,hUH⟩ := FiniteDifference.C1_of_controlled_normalized μ
    (by positivity : 0<r/4) ha hnorm
  have hC2:ContDiffOn ℝ 2 (fderiv ℝ u) (ball c (r/4)) := by
    rw [show (2:ℕ∞ω)=1+1 from by norm_num,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    exact ⟨(hu.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiable one_ne_zero |>.differentiableOn,by simp,hC1⟩
  have hC3:ContDiffOn ℝ 3 u (ball c (r/4)) := by
    rw [show (3:ℕ∞ω)=2+1 from by norm_num,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    exact ⟨(hu.differentiable (by norm_num : (2:ℕ∞ω)≠0)).differentiableOn,by simp,hC2⟩
  exact ⟨r/4,by positivity,hC3,U,hU,hUH⟩
end LinearSchauder
end



noncomputable section
namespace HolderJets
open Set Metric
open scoped ContDiff
universe u
variable {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma Local.of_C1 {f:E→F} (hf:ContDiff ℝ 1 f) : Local f := by
  intro c
  exact ⟨1/2,1,by norm_num,by norm_num,by norm_num,
    HolderControl.compact_convex_C1 (by norm_num) (by norm_num)
      (isCompact_closedBall c 1) (convex_closedBall c 1) hf⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
lemma restrict_exponent {f:E→F} {a d r R:ℝ} {c:E} (hd:0≤d) (hda:d≤a)
    (hr:r≤R) (hr1:r≤1/2)
    (hf:HolderControl.Controlled a (closedBall c R) (fun _:Unit => f)) :
    HolderControl.Controlled d (closedBall c r) (fun _:Unit => f) := by
  obtain ⟨B,C,hB,hC,hb,hc⟩ := hf
  have sub:closedBall c r⊆closedBall c R := closedBall_subset_closedBall hr
  refine ⟨B,C,hB,hC,fun j x hx=>hb j x (sub hx),?_⟩
  intro j x hx y hy
  apply (hc j x (sub hx) y (sub hy)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_ge' dist_nonneg _ hd hda
  have ht := dist_triangle x c y
  rw [dist_comm c y] at ht
  linarith [mem_closedBall.mp hx,mem_closedBall.mp hy]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
lemma Local.common {f:E→F} {g:E→G} (hf:Local f) (hg:Local g) (c:E) :
    ∃a r:ℝ,0<a ∧ a<1 ∧ 0<r ∧
      HolderControl.Controlled a (closedBall c r) (fun _:Unit=>f) ∧
      HolderControl.Controlled a (closedBall c r) (fun _:Unit=>g) := by
  obtain ⟨a,R,ha,ha1,hR,hf⟩ := hf c
  obtain ⟨d,S,hd,_,hS,hg⟩ := hg c
  refine ⟨min a d,min (min R S) (1/2),lt_min ha hd,
    (min_le_left _ _).trans_lt ha1,lt_min (lt_min hR hS) (by norm_num),?_,?_⟩
  · exact restrict_exponent (le_of_lt (lt_min ha hd)) (min_le_left _ _)
      ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _) hf
  · exact restrict_exponent (le_of_lt (lt_min ha hd)) (min_le_right _ _)
      ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _) hg

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma Local.linear (T:F→L[ℝ]G) {f:E→F} (hf:Local f) : Local (fun x=>T (f x)) := by
  intro c
  obtain ⟨a,r,ha,ha1,hr,hf⟩ := hf c
  exact ⟨a,r,ha,ha1,hr,hf.linear T⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
lemma Local.add {f g:E→F} (hf:Local f) (hg:Local g) : Local (fun x=>f x+g x) := by
  intro c
  obtain ⟨a,r,ha,ha1,hr,hf,hg⟩ := hf.common hg c
  exact ⟨a,r,ha,ha1,hr,hf.add hg⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma Local.bilinear (T:F→L[ℝ]G→L[ℝ]H) {f:E→F} {g:E→G}
    (hf:Local f) (hg:Local g) : Local (fun x=>T (f x) (g x)) := by
  intro c
  obtain ⟨a,r,ha,ha1,hr,hf,hg⟩ := hf.common hg c
  exact ⟨a,r,ha,ha1,hr,hf.bilinear T hg⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma Local.comp_C1 {f:E→F} {g:F→G} (hc:Continuous f) (hf:Local f)
    (hg:∀x,ContDiffAt ℝ 1 g (f x)) : Local (g∘f) := by
  intro c
  obtain ⟨a,R,ha,ha1,hR,B,C,hB,hC,hb,hholder⟩ := hf c
  obtain ⟨K,t,ht,hK⟩ := (hg c).exists_lipschitzOnWith
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds ht)
  let s:=min R r/2
  have hs:0<s := div_pos (lt_min hR hr) (by norm_num)
  have hsR:s≤R := by dsimp only [s]; linarith [min_le_left R r]
  have hsr:s<r := by dsimp only [s]; linarith [min_le_right R r]
  have hst (x:E) (hx:x∈closedBall c s) : f x∈t := hsub (mem_ball.mpr
    ((mem_closedBall.mp hx).trans_lt hsr))
  have hcR:c∈closedBall c R := mem_closedBall_self hR.le
  have hcs:c∈closedBall c s := mem_closedBall_self hs.le
  refine ⟨a,s,ha,ha1,hs,‖g (f c)‖+K*(2*B),K*C,by positivity,by positivity,?_,?_⟩
  · intro _ x hx
    have hdist := hK.dist_le_mul (f x) (hst x hx) (f c) (hst c hcs)
    have hn : dist (f x) (f c)≤2*B := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hb () x (closedBall_subset_closedBall hsR hx),hb () c hcR])
    have htriangle := norm_le_insert (g (f c)) (g (f x))
    rw [←dist_eq_norm,dist_comm] at htriangle
    change ‖g (f x)‖≤_
    linarith [mul_le_mul_of_nonneg_left hn K.coe_nonneg]
  · intro _ x hx y hy
    exact (hK.dist_le_mul (f x) (hst x hx) (f y) (hst y hy)).trans
      ((mul_le_mul_of_nonneg_left (hholder () x (closedBall_subset_closedBall hsR hx)
        y (closedBall_subset_closedBall hsR hy)) K.coe_nonneg).trans_eq (by ring))

omit [FiniteDimensional ℝ E] in
lemma Regular.contDiff {n:ℕ} {f:E→F} (hf:Regular n f) : ContDiff ℝ n f := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr hf.1
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    exact ⟨hf.1,by simp,ih hf.2⟩

omit [FiniteDimensional ℝ E] in
lemma Regular.continuous {n:ℕ} {f:E→F} (hf:Regular n f) : Continuous f := hf.contDiff.continuous

lemma Regular.local {n:ℕ} {f:E→F} (hf:Regular n f) : Local f := by
  cases n with
  | zero => exact hf.2
  | succ n => exact Local.of_C1 (hf.contDiff.of_le (by exact_mod_cast Nat.succ_pos n))

lemma Regular.pred {n:ℕ} {f:E→F} (hf:Regular (n+1) f) : Regular n f := by
  induction n generalizing F with
  | zero => exact ⟨hf.continuous,hf.local⟩
  | succ n ih => exact ⟨hf.1,ih hf.2⟩

omit [FiniteDimensional ℝ E] in
lemma Regular.linear (T:F→L[ℝ]G) {n:ℕ} {f:E→F} (hf:Regular n f) :
    Regular n (fun x=>T (f x)) := by
  induction n generalizing F G with
  | zero => exact ⟨T.continuous.comp hf.1,hf.2.linear T⟩
  | succ n ih =>
    have he: fderiv ℝ (fun x=>T (f x))=fun x=>T.comp (fderiv ℝ f x) := by
      funext x; exact (T.hasFDerivAt.comp x (hf.1 x).hasFDerivAt).fderiv
    exact ⟨T.differentiable.comp hf.1,he ▸ ih (ContinuousLinearMap.compL ℝ E F G T) hf.2⟩

omit [FiniteDimensional ℝ E] in
lemma Regular.add {n:ℕ} {f g:E→F} (hf:Regular n f) (hg:Regular n g) :
    Regular n (fun x=>f x+g x) := by
  induction n generalizing F with
  | zero => exact ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  | succ n ih =>
    have he:fderiv ℝ (fun x=>f x+g x)=fun x=>fderiv ℝ f x+fderiv ℝ g x := by
      funext x; exact ((hf.1 x).hasFDerivAt.add (hg.1 x).hasFDerivAt).fderiv
    exact ⟨hf.1.add hg.1,he ▸ ih hf.2 hg.2⟩

lemma Regular.bilinear (T:F→L[ℝ]G→L[ℝ]H) {n:ℕ} {f:E→F} {g:E→G}
    (hf:Regular n f) (hg:Regular n g) : Regular n (fun x=>T (f x) (g x)) := by
  induction n generalizing F G H with
  | zero => exact ⟨(T.continuous.comp hf.1).clm_apply hg.1,hf.2.bilinear T hg.2⟩
  | succ n ih =>
    have he:fderiv ℝ (fun x=>T (f x) (g x))=fun x=>
        T.precompR E (f x) (fderiv ℝ g x)+T.precompL E (fderiv ℝ f x) (g x) := by
      funext x; exact T.fderiv_of_bilinear (hf.1 x) (hg.1 x)
    refine ⟨fun x=>(T.hasFDerivAt_of_bilinear (hf.1 x).hasFDerivAt (hg.1 x).hasFDerivAt).differentiableAt,?_⟩
    rw [he]
    exact (ih (T.precompR E) hf.pred hg.2).add (ih (T.precompL E) hf.2 hg.pred)

lemma Regular.comp_smooth {n:ℕ} {f:E→F} {g:F→G} (hf:Regular n f)
    (hg:∀x,ContDiffAt ℝ ∞ g (f x)) : Regular n (g∘f) := by
  induction n generalizing F G with
  | zero =>
    exact ⟨continuous_iff_continuousAt.mpr (fun x=>(hg x).continuousAt.comp hf.1.continuousAt),
      hf.2.comp_C1 hf.1 (fun x=>(hg x).of_le (by simp))⟩
  | succ n ih =>
    have hdg (x:E) := (hg x).differentiableAt (by simp : (∞:ℕ∞ω)≠0)
    have he:fderiv ℝ (g∘f)=fun x=>(fderiv ℝ g (f x)).comp (fderiv ℝ f x) := by
      funext x; exact ((hdg x).hasFDerivAt.comp x (hf.1 x).hasFDerivAt).fderiv
    refine ⟨fun x=>(hdg x).comp x (hf.1 x),?_⟩
    rw [he]
    exact (ih hf.pred (fun x=>(hg x).fderiv_right (m:=∞) (by simp))).bilinear
      (ContinuousLinearMap.compL ℝ E F G) hf.2

lemma Regular.of_Cnext {n:ℕ} {f:E→F} (hf:ContDiff ℝ (n+1) f) : Regular n f := by
  induction n generalizing F with
  | zero => exact ⟨hf.continuous,Local.of_C1 (by simpa using hf)⟩
  | succ n ih =>
    exact ⟨hf.differentiable (by simp),ih (hf.fderiv_right (m:=n+1) (by simp [Nat.cast_add]))⟩

lemma Regular.of_smooth {n:ℕ} {f:E→F} (hf:ContDiff ℝ ∞ f) : Regular n f :=
  Regular.of_Cnext (n:=n) (hf.of_le (by exact_mod_cast (le_top : (n+1:ℕ∞)≤⊤)))

lemma Regular.mono {n m:ℕ} {f:E→F} (hf:Regular n f) (hm:m≤n) : Regular m f := by
  induction n generalizing F m with
  | zero =>
    have he:m=0:=by omega
    subst m
    exact hf
  | succ n ih =>
    cases m with
    | zero => exact ⟨hf.continuous,hf.local⟩
    | succ m => exact ⟨hf.1,ih hf.2 (by omega)⟩

omit [FiniteDimensional ℝ E] in
lemma Regular.prod {n:ℕ} {f:E→F} {g:E→G} (hf:Regular n f) (hg:Regular n g) :
    Regular n (fun x=>(f x,g x)) := by
  simpa only [ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,
    add_zero,zero_add] using
    (hf.linear (ContinuousLinearMap.inl ℝ F G)).add (hg.linear (ContinuousLinearMap.inr ℝ F G))

lemma Regular.sum {ι:Type*} (s:Finset ι) {n:ℕ} {f:ι→E→F} (hf:∀i∈s,Regular n (f i)) :
    Regular n (fun x=>∑i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Regular.of_smooth (n:=n) (contDiff_const (c:=(0:F))))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

lemma Regular.clm_of_basis {ι:Type*} [Fintype ι] (b:Module.Basis ι ℝ F)
    [FiniteDimensional ℝ F] {n:ℕ} {f:E→F→L[ℝ]G}
    (hf:∀i,Regular n (fun x=>f x (b i))) : Regular n f := by
  let T:ι→G→L[ℝ]F→L[ℝ]G := fun i=>ContinuousLinearMap.smulRightL ℝ F G
    (b.coord i).toContinuousLinearMap
  have hs:Regular n (fun x=>∑i,T i (f x (b i))) := Regular.sum Finset.univ
    (fun i _=>(hf i).linear (T i))
  have he:(fun x=>∑i,T i (f x (b i)))=f := by
    funext x
    ext v
    simp only [sum_apply]
    change (∑i,(b.repr v i) • f x (b i))=f x v
    simpa only [map_sum,map_smul] using congrArg (f x) (b.sum_repr v)
  rwa [he] at hs

end HolderJets


namespace HessianDirectional
open scoped ContDiff
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "Hes" => HessianInterpolation.hessian

lemma derivative_direction {u:E→F} (hu:ContDiff ℝ 3 u) (v x:E) :
    Hes (fun x=>fderiv ℝ u x v) x = (fderiv ℝ (Hes u) x v) := by
  have hD:ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hH:ContDiff ℝ 1 (Hes u) := hD.fderiv_right (by norm_num)
  have hd:=hD.differentiable (by norm_num : (2:ℕ∞ω)≠0)
  have hh:=hH.differentiable one_ne_zero
  let T:(E→L[ℝ]F)→L[ℝ]F:=ContinuousLinearMap.apply ℝ F v
  have hfirst : fderiv ℝ (fun x=>fderiv ℝ u x v)=fun x=>T.comp (Hes u x) := by
    funext x
    exact (T.hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv
  have hsecond : Hes (fun x=>fderiv ℝ u x v) x=
      (ContinuousLinearMap.compL ℝ E (E→L[ℝ]F) F T).comp (fderiv ℝ (Hes u) x) := by
    unfold HessianInterpolation.hessian
    rw [hfirst]
    exact ((ContinuousLinearMap.compL ℝ E (E→L[ℝ]F) F T).hasFDerivAt.comp x (hh x).hasFDerivAt).fderiv
  have hs (y z:E) : fderiv ℝ (Hes u) x y z v=fderiv ℝ (Hes u) x y v z := by
    have he:(fun t=>Hes u t z v)=(fun t=>Hes u t v z) := by
      funext t
      exact hu.contDiffAt.isSymmSndFDerivAt (by norm_num) z v
    have hze:=congrArg (fun f:E→F=>fderiv ℝ f x y) he
    simpa only [fderiv_clm_apply (hh x) (differentiableAt_const _),
      fderiv_clm_apply ((hh x).clm_apply (differentiableAt_const _)) (differentiableAt_const _),
      fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
      ContinuousLinearMap.flip_apply] using hze
  ext y z
  rw [hsecond]
  change fderiv ℝ (Hes u) x y z v=fderiv ℝ (Hes u) x v y z
  rw [hs]
  exact congrArg (fun T:E→L[ℝ]F=>T z)
    (hD.contDiffAt.isSymmSndFDerivAt (by norm_num) y v)
end HessianDirectional


namespace LinearSchauder
open Set Metric HolderJets
open scoped ContDiff InnerProductSpace
variable {E:Type} {ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
local notation "Hes" => HessianInterpolation.hessian

attribute [local instance] OAI.LinearSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
attribute [local instance] OAI.LinearSchauder.instNormedSpaceRealContinuousLinearMapId_solutions_2
attribute [local instance] OAI.LinearSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions_3
attribute [local instance] OAI.LinearSchauder.instNormedSpaceRealContinuousLinearMapId_solutions_3
attribute [local instance] OAI.LinearSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions_4
attribute [local instance] OAI.LinearSchauder.instNormedSpaceRealContinuousLinearMapId_solutions_4
attribute [local instance] OAI.LinearSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions_5
attribute [local instance] OAI.LinearSchauder.instNormedSpaceRealContinuousLinearMapId_solutions_5
lemma regular_three (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (b:OrthonormalBasis ι ℝ E) {u S:E→ℝ} {A:E→E→L[ℝ]E}
    (hu:Regular 2 u) (hA:Regular 1 A) (hS:Regular 1 S)
    (heq:∀x,CoefficientTrace.trace b (Hes u x) (A x)=S x)
    (hp:∀c x:E,x≠0 → 0<⟪x,A c x⟫_ℝ) : Regular 3 u := by
  have hH:Local (Hes u) := hu.2.2.2
  have hDA:Regular 0 (fderiv ℝ A) := hA.2
  have hDS:Regular 0 (fderiv ℝ S) := hS.2
  have hdata:Local (fun x=>(fderiv ℝ A x,fderiv ℝ S x)) := (hDA.prod hDS).local
  have hgain (c:E) : ∃a r:ℝ,0<a ∧ a<1 ∧ 0<r ∧ ContDiffOn ℝ 3 u (ball c r) ∧
      ∃U:ℝ,0≤U ∧ ∀x∈ball c r,∀y∈ball c r,
        dist (fderiv ℝ (Hes u) x) (fderiv ℝ (Hes u) y)≤U*dist x y^a := by
    obtain ⟨a,r,ha,ha1,hr,hh,hd⟩ := hH.common hdata c
    have hda:=hd.linear (ContinuousLinearMap.fst ℝ (E→L[ℝ]E→L[ℝ]E) (E→L[ℝ]ℝ))
    have hds:=hd.linear (ContinuousLinearMap.snd ℝ (E→L[ℝ]E→L[ℝ]E) (E→L[ℝ]ℝ))
    obtain ⟨s,hs,hu3,hhold⟩ := C3_local μ b hu.contDiff hA.contDiff hS.contDiff heq
      (hp c) hr ha ha1 hh hda hds
    exact ⟨a,s,ha,ha1,hs,hu3,hhold⟩
  have hu3:ContDiff ℝ 3 u := contDiff_iff_contDiffAt.mpr (fun c=>by
    obtain ⟨a,r,ha,ha1,hr,hc,hhold⟩ := hgain c
    exact hc.contDiffAt (ball_mem_nhds c hr))
  have hHC:ContDiff ℝ 1 (Hes u) :=
    (hu3.fderiv_right (m:=2) (by norm_num)).fderiv_right (by norm_num)
  have hDHC:Continuous (fderiv ℝ (Hes u)) := (contDiff_one_iff_fderiv.mp hHC).2
  refine ⟨hu.1,hu.2.1,hHC.differentiable one_ne_zero,hDHC,?_⟩
  intro c
  obtain ⟨a,r,ha,ha1,hr,_,C,hC,hhold⟩ := hgain c
  obtain ⟨B,hB⟩ := (isCompact_closedBall c (r/2)).exists_bound_of_continuousOn hDHC.continuousOn
  have hsub:closedBall c (r/2)⊆ball c r := closedBall_subset_ball (by linarith)
  exact ⟨a,r/2,ha,ha1,by positivity,max 0 B,C,le_max_left _ _,hC,
    fun _ x hx=>(hB x hx).trans (le_max_right _ _),fun _ x hx y hy=>hhold x (hsub hx) y (hsub hy)⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma differentiated_equation (b:OrthonormalBasis ι ℝ E) {u S:E→ℝ} {A:E→E→L[ℝ]E}
    (hu:ContDiff ℝ 3 u) (hA:Differentiable ℝ A) (_hS:Differentiable ℝ S)
    (heq:∀x,CoefficientTrace.trace b (Hes u x) (A x)=S x) (v x:E) :
    CoefficientTrace.trace b (Hes (fun z=>fderiv ℝ u z v) x) (A x)=
      fderiv ℝ S x v-CoefficientTrace.trace b (Hes u x) (fderiv ℝ A x v) := by
  have hH:ContDiff ℝ 1 (Hes u) :=
    (hu.fderiv_right (m:=2) (by norm_num)).fderiv_right (by norm_num)
  have he:(fun x=>CoefficientTrace.bilinear b (Hes u x) (A x))=S := funext heq
  have hd:HasFDerivAt S ((CoefficientTrace.bilinear b).precompR E (Hes u x) (fderiv ℝ A x)+
      (CoefficientTrace.bilinear b).precompL E (fderiv ℝ (Hes u) x) (A x)) x := by
    rw [←he]
    exact (CoefficientTrace.bilinear b).hasFDerivAt_of_bilinear
      (hH.differentiable one_ne_zero x).hasFDerivAt (hA x).hasFDerivAt
  have hv:=congrArg (fun T:E→L[ℝ]ℝ=>T v) hd.fderiv
  rw [HessianDirectional.derivative_direction hu v x]
  change CoefficientTrace.bilinear b (fderiv ℝ (Hes u) x v) (A x)=
    fderiv ℝ S x v-CoefficientTrace.bilinear b (Hes u x) (fderiv ℝ A x v)
  change fderiv ℝ S x v=CoefficientTrace.bilinear b (Hes u x) (fderiv ℝ A x v)+
    CoefficientTrace.bilinear b (fderiv ℝ (Hes u) x v) (A x) at hv
  linarith

theorem higher (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (b:OrthonormalBasis ι ℝ E) (n:ℕ) {u S:E→ℝ} {A:E→E→L[ℝ]E}
    (hu:Regular 2 u) (hA:Regular (n+1) A) (hS:Regular (n+1) S)
    (heq:∀x,CoefficientTrace.trace b (Hes u x) (A x)=S x)
    (hp:∀c x:E,x≠0 → 0<⟪x,A c x⟫_ℝ) : Regular (n+3) u := by
  induction n generalizing u S with
  | zero => exact regular_three μ b hu hA hS heq hp
  | succ n ih =>
    have hug:Regular (n+3) u := ih hu hA.pred hS.pred heq
    have hu3:ContDiff ℝ 3 u := (hug.mono (m:=3) (by omega)).contDiff
    have hDu:Regular (n+2) (fderiv ℝ u) := hug.2
    have hHu:Regular (n+1) (Hes u) := hDu.2
    have hdirs (v:E) : Regular (n+3) (fun x=>fderiv ℝ u x v) := by
      let Sv:E→ℝ:=fun x=>fderiv ℝ S x v-
        CoefficientTrace.trace b (Hes u x) (fderiv ℝ A x v)
      have hSv:Regular (n+1) Sv := by
        have h₁:=hS.2.linear (ContinuousLinearMap.apply ℝ ℝ v)
        have h₂:=hHu.bilinear (CoefficientTrace.bilinear b)
          (hA.2.linear (ContinuousLinearMap.apply ℝ (E→L[ℝ]E) v))
        exact h₁.add (h₂.linear (-ContinuousLinearMap.id ℝ ℝ))
      apply ih ((hDu.mono (m:=2) (by omega)).linear (ContinuousLinearMap.apply ℝ ℝ v)) hA.pred hSv
      exact differentiated_equation b hu3 (hA.mono (by omega : 1≤n+1+1)).1
        (hS.mono (by omega : 1≤n+1+1)).1 heq v
    exact ⟨hug.1,Regular.clm_of_basis b.toBasis (fun i=>hdirs (b i))⟩

end LinearSchauder


namespace MomentSchauder
open Set Metric Matrix InnerProductSpace HolderJets MomentQuotient
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
variable {E:Type} {ι:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
local notation "Hes" => HessianInterpolation.hessian
local notation "Mat" => Matrix ι ι ℝ

attribute [local instance] OAI.MomentSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.MomentSchauder.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.MomentSchauder.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.MomentSchauder.instNormedSpaceRealContinuousLinearMapId_solutions_1
omit [MeasurableSpace E] [BorelSpace E] in
lemma scalarToVector_hessian {u:E→ℝ} (hu:ContDiff ℝ 2 u) (x:E) :
    scalarToVector (Hes u x)=fderiv ℝ (gradient u) x := by
  have hDu:=hu.fderiv_right (m:=1) (by norm_num)
  exact ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    (hDu.differentiable one_ne_zero x).hasFDerivAt).fderiv.symm

attribute [local instance] OAI.MomentSchauder.instTopologicalSpaceMatrixReal_solutions
omit [MeasurableSpace E] [BorelSpace E] in
lemma scalarToMatrix_hessian (b:OrthonormalBasis ι ℝ E) {u:E→ℝ} (hu:ContDiff ℝ 2 u) (x:E) :
    scalarToMatrix b (Hes u x)=matrixHessian b u x := by
  change (HessianTrace.fromMatrix b).symm (scalarToVector (Hes u x))=_
  rw [scalarToVector_hessian hu]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma inverse_smooth_at {A:Mat} (ha:A.det≠0) : ContDiffAt ℝ ∞ (fun M:Mat=>M⁻¹) A := by
  have hadj:ContDiff ℝ ∞ (fun M:Mat=>M.adjugate) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp_rw [Matrix.adjugate_apply]
    apply MomentDifferential.smooth_det.comp
    apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro l
    by_cases h:j=k
    · subst k
      simp only [Matrix.updateRow_apply,ite_true]
      exact contDiff_const
    · simp only [Matrix.updateRow_apply,ite_eq_right (Ne.symm h)]
      let ev : Mat →L[ℝ] ℝ :=
        ({ toFun := fun M => M k l
           map_add' := fun M N => rfl
           map_smul' := fun r M => rfl } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap
      exact ev.contDiff
  have hi := (MomentDifferential.smooth_det.contDiffAt.inv ha).smul hadj.contDiffAt
  convert hi using 1
  ext M i j
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma trace_scalar_matrix (b:OrthonormalBasis ι ℝ E) {u:E→ℝ} (hu:ContDiff ℝ 2 u)
    (A:Mat) (x:E) : CoefficientTrace.trace b (Hes u x) (HessianTrace.fromMatrix b A)=
      (A*scalarToMatrix b (Hes u x)).trace := by
  rw [HessianTrace.trace_eq_matrix hu,scalarToMatrix_hessian b hu]
  congr 2
  exact (HessianTrace.fromMatrix b).symm_apply_apply A

omit [MeasurableSpace E] [BorelSpace E] in

lemma equation (b:OrthonormalBasis ι ℝ E) {u V:E→ℝ} (hu:ContDiff ℝ 3 u)
    (hV:Differentiable ℝ V) {d:ℝ}
    (heq:∀x,Real.log (matrixHessian b u x).det=V (gradient u x)+d-u x)
    (hp:∀x,(matrixHessian b u x).PosDef) (v x:E) :
    CoefficientTrace.trace b (Hes (fun y=>fderiv ℝ u y v) x)
      (HessianTrace.fromMatrix b ((matrixHessian b u x)⁻¹))=
      fderiv ℝ V (gradient u x) (scalarToVector (Hes u x) v)-fderiv ℝ u x v := by
  have hu2:ContDiff ℝ 2 u:=hu.of_le (by norm_num)
  have hDu:ContDiff ℝ 2 (fderiv ℝ u):=hu.fderiv_right (by norm_num)
  have hH:ContDiff ℝ 1 (Hes u):=hDu.fderiv_right (by norm_num)
  have hM:ContDiff ℝ 1 (matrixHessian b u) := by
    have he:matrixHessian b u=fun y=>scalarToMatrix b (Hes u y):=funext fun y=>(scalarToMatrix_hessian b hu2 y).symm
    rw [he]
    exact (scalarToMatrix b).contDiff.comp hH
  have hMD:fderiv ℝ (matrixHessian b u) x=
      (scalarToMatrix b).comp (fderiv ℝ (Hes u) x) := by
    have he:matrixHessian b u=fun y=>scalarToMatrix b (Hes u y):=funext fun y=>(scalarToMatrix_hessian b hu2 y).symm
    rw [he]
    exact ((scalarToMatrix b).hasFDerivAt.comp x (hH.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hlog:=((MomentDifferential.detMultilinear.hasFDerivAt (matrixHessian b u x)).comp x
    (hM.differentiable one_ne_zero x).hasFDerivAt).log (hp x).det_pos.ne'
  have hg:ContDiff ℝ 2 (gradient u) :=
    (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hDu
  have hr:=(((hV (gradient u x)).hasFDerivAt.comp x (hg.differentiable (by norm_num) x).hasFDerivAt).add_const d).sub
    (hu.differentiable (by norm_num) x).hasFDerivAt
  have hfun:(fun y=>Real.log (matrixHessian b u y).det)=(fun y=>V (gradient u y)+d-u y):=funext heq
  change HasFDerivAt (fun y=>Real.log (matrixHessian b u y).det)
    ((matrixHessian b u x).det⁻¹ •
      (MomentDifferential.detMultilinear.linearDeriv (matrixHessian b u x)).comp
        (fderiv ℝ (matrixHessian b u) x)) x at hlog
  rw [hfun] at hlog
  have hd:=congrArg (fun T:E→L[ℝ]ℝ=>T v) (hlog.unique hr)
  have hmat: (((matrixHessian b u x)⁻¹)*scalarToMatrix b (fderiv ℝ (Hes u) x v)).trace=
      (((matrixHessian b u x).adjugate)*scalarToMatrix b (fderiv ℝ (Hes u) x v)).trace /
        (matrixHessian b u x).det := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,div_eq_mul_inv]
    ring
  have hv2:ContDiff ℝ 2 (fun y=>fderiv ℝ u y v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp hDu
  rw [trace_scalar_matrix b hv2,
    HessianDirectional.derivative_direction hu,hmat]
  rw [scalarToVector_hessian hu2]
  change (matrixHessian b u x).det⁻¹ *
    MomentDifferential.detMultilinear.linearDeriv (matrixHessian b u x)
      (fderiv ℝ (matrixHessian b u) x v) =
        fderiv ℝ V (gradient u x) (fderiv ℝ (gradient u) x v)-fderiv ℝ u x v at hd
  rw [hMD,ContinuousLinearMap.comp_apply,MomentDifferential.det_linearDeriv] at hd
  simpa only [div_eq_mul_inv,mul_comm] using hd

theorem smooth_of_regular_three_oai (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (b:OrthonormalBasis ι ℝ E) {u V:E→ℝ} (hu:Regular 3 u) (hV:ContDiff ℝ ∞ V)
    {d:ℝ} (heq:∀x,Real.log (matrixHessian b u x).det=V (gradient u x)+d-u x)
    (hp:∀x,(matrixHessian b u x).PosDef) : ContDiff ℝ ∞ u := by
  have hu3:ContDiff ℝ 3 u:=hu.contDiff
  have hu2:ContDiff ℝ 2 u:=hu3.of_le (by norm_num)
  let A:E→E→L[ℝ]E:=fun x=>HessianTrace.fromMatrix b ((matrixHessian b u x)⁻¹)
  have hAp(c x:E)(hx:x≠0):0<⟪x,A c x⟫_ℝ:=HessianTrace.inner_pos_fromMatrix b (hp c).inv x hx
  have hreg (n:ℕ):Regular (n+3) u := by
    induction n with
    | zero => exact hu
    | succ n ih =>
      have hDu:Regular (n+2) (fderiv ℝ u):=ih.2
      have hHu:Regular (n+1) (Hes u):=hDu.2
      have hM:Regular (n+1) (matrixHessian b u) := by
        have hm:=hHu.linear (scalarToMatrix b)
        simpa only [scalarToMatrix_hessian b hu2] using hm
      have hA:Regular (n+1) A := (hM.comp_smooth (fun x=>inverse_smooth_at (hp x).det_pos.ne')).linear
        (HessianTrace.fromMatrix b).toContinuousLinearMap
      have hgu:Regular (n+1) (gradient u) :=
        (hDu.mono (by omega)).linear (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hDV:Regular (n+1) (fun x=>fderiv ℝ V (gradient u x)) :=
        hgu.comp_smooth (fun _=>(hV.fderiv_right (m:=∞) (by simp)).contDiffAt)
      have hdirs(v:E):Regular (n+3) (fun x=>fderiv ℝ u x v) := by
        let S:E→ℝ:=fun x=>fderiv ℝ V (gradient u x) (scalarToVector (Hes u x) v)-fderiv ℝ u x v
        have hS:Regular (n+1) S := by
          have hgv:Regular (n+1) (fun x=>scalarToVector (Hes u x) v):=
            (hHu.linear scalarToVector).linear (ContinuousLinearMap.apply ℝ E v)
          have hP:=hDV.bilinear (ContinuousLinearMap.apply ℝ ℝ).flip hgv
          exact hP.add (((hDu.mono (by omega)).linear (ContinuousLinearMap.apply ℝ ℝ v)).linear
            (-ContinuousLinearMap.id ℝ ℝ))
        apply LinearSchauder.higher μ b n
          ((hu.2:Regular 2 (fderiv ℝ u)).linear (ContinuousLinearMap.apply ℝ ℝ v)) hA hS
          (equation b hu3 (hV.differentiable (by simp)) heq hp v) hAp
      exact ⟨hu.1,Regular.clm_of_basis b.toBasis (fun i=>hdirs (b i))⟩
  rw [contDiff_infty]
  intro n
  exact (hreg n).contDiff.of_le (by exact_mod_cast (show n≤n+3 by omega))

end MomentSchauder


end



end OAI
end

theorem solution : type_of% @OAI.MomentSchauder.smooth_of_regular_three_oai := @OAI.MomentSchauder.smooth_of_regular_three_oai
