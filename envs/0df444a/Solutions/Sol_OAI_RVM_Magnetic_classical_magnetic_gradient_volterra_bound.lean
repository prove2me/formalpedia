-- Prove2me | solution 1 for OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:39:26.15588+00:00
-- url     : https://prove2.me/submissions/79053977-d7da-4518-8f72-67e03905cfb9

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Magnetic_magnetic_source_particle_gradient_volterra_bound
import Theorems.Thm_OAI_RVM_Magnetic_magnetic_transport_deriv_bound
import Theorems.Thm_OAI_RVM_classical_shifted_magnetic_physical_representation_before
import Theorems.Thm_OAI_RVM_datum_boundary_global_jets_horizon

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

lemma particle_differentiableAt_positive {s : Solution}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    DifferentiableAt ℝ s.f (t,x,v) := by
  have hnhds : particleHalfSpace ∈ nhds (t,x,v) := by
    have hopen : IsOpen {z : ℝ × Phase | 0 < z.1} :=
      isOpen_lt continuous_const continuous_fst
    apply Filter.mem_of_superset (hopen.mem_nhds ht)
    intro z hz
    change 0 ≤ z.1
    exact le_of_lt hz
  exact ((hreg (t,x,v) ht.le).contDiffAt hnhds).differentiableAt (by norm_num)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma contDiff_lorentz (E B : Vec) {k : ℕ∞ω} :
    ContDiff ℝ k (fun v => E+cross (velocity v) B) := by
  exact contDiff_const.add (contDiff_cross.comp (contDiff_velocity.prodMk contDiff_const))

lemma hasFDerivAt_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasFDerivAt (fun x => ∫ v : Vec, F (x,v))
      ((∫ v : Vec, fderiv ℝ F (p,v)).comp (ContinuousLinearMap.inl ℝ H Vec)) p := by
  have h := hasFDerivAt_convolution_right_with_param
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (g := fun x v => F (x,v)) hU hK (fun x v hx hv => hzero x hx v hv)
    (locallyIntegrable_const (1 : ℝ)) hF (p,0) hp
  have hi : HasFDerivAt (fun x : H => (x,(0 : Vec)))
      (ContinuousLinearMap.inl ℝ H Vec) p := by
    convert (hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : Vec) p) using 1 <;> rfl
  have hc := h.comp p hi
  have hls : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W) 1 =
      ContinuousLinearMap.id ℝ W := by ext w; simp
  change HasFDerivAt (fun x => convolution (fun _ => (1 : ℝ)) (fun v => F (x,v))
    (ContinuousLinearMap.lsmul ℝ ℝ) volume 0)
    ((convolution (fun _ => (1 : ℝ)) (fun v => fderiv ℝ F (p,v))
      (ContinuousLinearMap.precompR (H × Vec) (ContinuousLinearMap.lsmul ℝ ℝ)) volume 0).comp
      (ContinuousLinearMap.inl ℝ H Vec)) p at hc
  simp only [convolution_def, zero_sub, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, hls,
    ContinuousLinearMap.id_comp] at hc
  have hn (x : H) : (∫ v : Vec, F (x,-v)) = ∫ v : Vec, F (x,v) :=
    integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  have hn' : (∫ v : Vec, fderiv ℝ F (p,-v)) = ∫ v : Vec, fderiv ℝ F (p,v) :=
    integral_neg_eq_self (fun v : Vec => fderiv ℝ F (p,v)) volume
  simpa only [hn, hn'] using hc

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

lemma compactSupport_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasCompactSupport (fun v : Vec => fderiv ℝ F (p,v)) := by
  apply compactSupport_of_zero_off hK
  intro v hv
  have hn : U ×ˢ Kᶜ ∈ 𝓝 (p,v) :=
    (hU.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp,hv⟩
  have hz : F =ᶠ[𝓝 (p,v)] (fun _ => 0) := by
    filter_upwards [hn] with y hy
    exact hzero y.1 hy.1 y.2 hy.2
  simpa only [fderiv_const_apply] using hz.fderiv_eq (𝕜 := ℝ)

lemma integrable_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    Integrable (fun v : Vec => fderiv ℝ F (p,v)) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_param_fderiv hU hK hp hzero)

lemma fderiv_integral_uniform_support_apply
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, F (x,v)) p b =
      ∫ v : Vec, fderiv ℝ F (p,v) (b,0) := by
  rw [(hasFDerivAt_integral_uniform_support hU hK hp hF hzero).fderiv]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
    (ContinuousLinearMap.integral_apply (integrable_param_fderiv hU hK hp hF hzero) (b,0))

lemma fderiv_weighted_param {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H × Vec → ℝ} {w : Vec → ℝ} {p : H} {v : Vec}
    (hF : DifferentiableAt ℝ F (p,v)) (hw : DifferentiableAt ℝ w v) (b : H) :
    fderiv ℝ (fun z : H × Vec => w z.2 * F z) (p,v) (b,0) =
      w v * fderiv ℝ F (p,v) (b,0) := by
  have hdw := hw.hasFDerivAt.comp (p,v) (hasFDerivAt_snd (𝕜 := ℝ) (p := (p,v)))
  have he := congrArg (fun L : (H × Vec) →L[ℝ] ℝ => L (b,0)) (hdw.mul hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun z : H × Vec => w z.2 * F z) (p,v) (b,0) =
    w v * fderiv ℝ F (p,v) (b,0) + F (p,v) * fderiv ℝ w v 0 at he
  simpa only [map_zero, mul_zero, add_zero] using he

lemma fderiv_weighted_integral_uniform_support_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H} {K : Set Vec} {F : H × Vec → ℝ} {p : H} {w : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) (hw : ContDiff ℝ 1 w)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, w v * F (x,v)) p b =
      ∫ v : Vec, w v * fderiv ℝ F (p,v) (b,0) := by
  have hG : ContDiffOn ℝ 1 (fun z : H × Vec => w z.2 * F z) (U ×ˢ univ) :=
    (hw.comp contDiff_snd).contDiffOn.mul hF
  rw [fderiv_integral_uniform_support_apply hU hK hp hG
    (fun x hx v hv => by simp only [hzero x hx v hv, mul_zero])]
  apply integral_congr_ae
  filter_upwards [] with v
  exact fderiv_weighted_param
    (((hF (p,v) ⟨hp,mem_univ _⟩).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hp,mem_univ _⟩)).differentiableAt (by simp))
    (hw.differentiable (by simp) v) b

lemma contDiff_reassociate {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : (ℝ × Vec) × Vec => (z.1.1,z.1.2,z.2)) :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)

lemma contDiffOn_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {n : ℕ∞} {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hU : IsOpen U) (hK : IsCompact K)
    (hF : ContDiffOn ℝ n F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContDiffOn ℝ n (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := contDiffOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) contDiffOn_const (g := fun x v => F (x,v))
    hU hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_WithinFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

section WithinFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasFDerivAt_time_slice {f : ℝ × E → E} {T : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E))) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (fun y => f (t,y))
      ((fderivWithin ℝ f (Icc 0 T ×ˢ (univ : Set E)) (t,x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hh := (hf.differentiableOn (by norm_num) (t,x) ⟨ht,mem_univ x⟩).hasFDerivWithinAt
  exact hh.comp_hasFDerivAt x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    (Filter.Eventually.of_forall (fun _ => ⟨ht,mem_univ _⟩))

lemma contDiffOn_spaceDerivative {f : ℝ × E → E} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E))) :
    ContDiffOn ℝ 1 (spaceDerivative f) (Icc 0 T ×ˢ (univ : Set E)) := by
  have hu : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set E)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hh := (hf.fderivWithin hu (m := 1) (by norm_num)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  apply hh.congr
  intro z hz
  exact (hasFDerivAt_time_slice (hf.of_le (by norm_num)) hz.1 z.2).fderiv

end WithinFlow


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open scoped Topology NNReal ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

open Set MeasureTheory Filter
open scoped Topology ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


open Set MeasureTheory Filter
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma continuousOn_integral_uniform_support
    {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hK : IsCompact K) (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContinuousOn (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := continuousOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) continuousOn_const (g := fun x v => F (x,v))
    hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma RegularParticle.slice {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => f (t,x,v)) ∧ HasCompactSupport (fun v : Vec => f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hf.1.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ht)
  · obtain ⟨K,hK,hz⟩ := hf.2 t ht
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hz t ⟨ht,le_rfl⟩ (subset_tsupport _ hn),rfl⟩

lemma RegularParticle.moment_continuous_slab {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (particleMoment f w) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, f (p.1,p.2,v) • w v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => f (z.1.1,z.1.2,z.2) • w z.2) (hK.image continuous_snd)
  · apply ContinuousOn.smul ?_ (hw.comp continuous_snd).continuousOn
    exact hf.1.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      (fun z hz => hz.1.1.1)
  · intro p hp v hv
    have hz : f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hz,zero_smul]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_Sphere
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology NNReal

namespace RVM

lemma integral_radial_measure {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) :
    (∫ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2) = ∫ r in Ioi (0 : ℝ), r^2 • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r => Real.toNNReal (r^2) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change (r^2).toNNReal • f r = r^2 • f r
    rw [NNReal.smul_def,Real.coe_toNNReal _ (sq_nonneg r)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma integrable_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Vec → W} (hf : Integrable f) :
    Integrable (fun p : Sphere × Ioi (0 : ℝ) => f (p.2.1 • p.1.1))
      (sphereMeasure.prod (Measure.volumeIoiPow 2)) := by
  have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
  simp only [Function.comp_def,Homeomorph.symm_apply_apply] at h
  have hi : Integrable (fun z : ({0}ᶜ : Set Vec) => f z.1) (volume.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have := h.mp hi
  simpa only [homeomorphUnitSphereProd_symm_apply_coe,finrank_euclideanSpace_fin,
    Nat.reduceSub] using this

lemma integral_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Vec → W} (hf : Integrable f) :
    (∫ y : Vec, f y) = ∫ n : Sphere, ∫ r in Ioi (0 : ℝ), r^2 • f (r • n.1) ∂volume ∂sphereMeasure := by
  calc
    _ = ∫ z : ({0}ᶜ : Set Vec), f z.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,restrict_compl_singleton]
    _ = ∫ p : Sphere × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
      simpa only [Homeomorph.symm_apply_apply,homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin,Nat.reduceSub] using h
    _ = ∫ n : Sphere, ∫ r : Ioi (0 : ℝ), f (r.1 • n.1) ∂Measure.volumeIoiPow 2
        ∂sphereMeasure := integral_prod _ (integrable_polar hf)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun n => integral_radial_measure (fun r => f (r • n.1)))
end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma hasFDerivAt_integral_sphere
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (p : H) :
    HasFDerivAt (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure)
      (∫ n : Sphere, (fderiv ℝ F (p,n.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
        ∂sphereMeasure) p := by
  let D : H × Sphere → H →L[ℝ] W := fun z =>
    (fderiv ℝ F (z.1,z.2.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
  have hD : Continuous D := by
    exact ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x n => D (x,n))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun n x hx => hC _ ⟨(x,n),⟨hx,mem_univ n⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun n x _ => (hF.differentiable (by simp) (x,n.1)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const n.1 x) using 1 <;> rfl))

lemma continuous_integral_sphere
    {H W : Type*} [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × Vec → W} (hF : Continuous F) :
    Continuous (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  have hc : Continuous (fun p : H × Sphere => F (p.1,p.2.1)) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc.continuousOn
  intro x n _ hn
  exact (hn (mem_univ n)).elim

lemma contDiff_integral_sphere_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W}, ContDiff ℝ k F →
      ContDiff ℝ k (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF
    exact contDiff_zero.mpr (continuous_integral_sphere hF.continuous)
  | succ k ih =>
    intro W _ _ _ F hF
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.succ_pos k)
    let D : H × Vec → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H Vec)
    have hD : ContDiff ℝ k D :=
      ((contDiff_succ_iff_fderiv.mp hF).2.2).clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) =
        (fun x => ∫ n : Sphere, D (x,n.1) ∂sphereMeasure) := by
      funext x
      exact (hasFDerivAt_integral_sphere hF1 x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_sphere hF1 x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD

lemma contDiff_integral_sphere
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_integral_sphere_nat k (contDiff_infty.mp hF k)

lemma contDiff_sphereSum {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sphereSum g) := by
  apply contDiff_integral_sphere (F:=fun p : (ℝ × Vec) × Vec => g (p.1.2+p.1.1 • p.2))
  exact hg.comp ((contDiff_snd.comp contDiff_fst).add
    ((contDiff_fst.comp contDiff_fst).smul contDiff_snd))

lemma sphereSum_radial_deriv {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (x : Vec) (r : ℝ) :
    HasDerivAt (fun t => sphereSum g (t,x))
      (∫ n : Sphere, fderiv ℝ g (x+r • n.1) n.1 ∂sphereMeasure) r := by
  let F : ℝ × Vec → ℝ := fun p => g (x+p.1 • p.2)
  have hF : ContDiff ℝ 1 F := hg.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))
  have hd := (hasFDerivAt_integral_sphere hF r).hasDerivAt
  have hDa (n : Sphere) : ((fderiv ℝ F (r,n.1)).comp
      (ContinuousLinearMap.inl ℝ ℝ Vec)) 1 = fderiv ℝ g (x+r • n.1) n.1 := by
    have hfst : HasFDerivAt (fun p : ℝ × Vec => p.1)
        (ContinuousLinearMap.fst ℝ ℝ Vec) (r,n.1) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun p : ℝ × Vec => p.2)
        (ContinuousLinearMap.snd ℝ ℝ Vec) (r,n.1) := hasFDerivAt_snd
    have hi := (hasFDerivAt_const x (r,n.1)).add (hfst.smul hsnd)
    have he := ((hg.differentiable (by simp)) (x+r • n.1)).hasFDerivAt.comp (r,n.1) hi
    change HasFDerivAt F _ (r,n.1) at he
    rw [he.fderiv]
    simp
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (r,n.1)).comp
      (ContinuousLinearMap.inl ℝ ℝ Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  rw [ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) 1] at hd
  simp_rw [hDa] at hd
  exact hd

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveK
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

lemma contDiff_waveK {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (waveK g) :=
  contDiff_const.mul (contDiff_fst.mul (contDiff_sphereSum hg))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ParamPrimitive
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : Differentiable ℝ F) (t : ℝ) (x : H) :
    deriv (fun r => F (r,x)) t = dirD F (1,0) (t,x) := by
  exact ((hF (t,x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) x t))).hasDerivAt.deriv

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma contDiff_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (i : Fin 3) : ContDiff ℝ ∞ (fun x => F x i) :=
  (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma integrableOn_norm_rpow_neg {α R : ℝ} (hα : α<3) :
    IntegrableOn (fun z : Vec => ‖z‖ ^ (-α)) (ball (0:Vec) R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp) (C:=1) (α:=α) (by simpa using hα)
  · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]; simp)
  · exact (continuous_norm.measurable.pow measurable_const).aestronglyMeasurable

lemma coneDirection_norm {x y : Vec} (h : x≠y) : ‖coneDirection x y‖=1 := by
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp [coneDirection,coneRadius,norm_smul,hr.ne']



section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

lemma contDiffAt_coneRadius {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneRadius x) y :=
  (contDiffAt_const.sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr hxy)

lemma contDiffAt_coneDirection {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneDirection x) y :=
  ((contDiffAt_coneRadius hxy).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))).smul
    (contDiffAt_const.sub contDiffAt_id)

lemma contDiffAt_retardedG {k : ℕ∞ω} {x y v : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (retardedG x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ k (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ k (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have hd : ContDiffAt ℝ k (fun z : Phase => 1-dot (coneDirection x z.1) (velocity z.2)) (y,v) :=
    contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu))
  exact ((hr.mul hd).inv (mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
    (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne')).smul (hn.sub hu)

lemma contDiffAt_retardedH {k : ℕ∞ω} {x y v : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (retardedH x) (y,v) :=
  contDiff_cross.contDiffAt.comp (y,v)
    (((contDiffAt_coneDirection (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst).prodMk
      (contDiffAt_retardedG hxy))

lemma contDiffAt_retardedDensity {k : ℕ∞ω} {f : Particle} {x y v : Vec} {t : ℝ}
    (hf : ContDiffAt ℝ k f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    ContDiffAt ℝ k (retardedDensity f t x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hm : ContDiffAt ℝ k (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((contDiffAt_const (c:=t)).sub hr).prodMk contDiffAt_id
  exact hf.comp (f:=fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hm

lemma particle_contDiffAt_positive {k : ℕ∞ω} {f : Particle}
    (hf : ContDiffOn ℝ k f particleHalfSpace) {t : ℝ} (ht : 0<t) (x v : Vec) :
    ContDiffAt ℝ k f (t,x,v) := by
  have hn : particleHalfSpace ∈ 𝓝 (t,x,v) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht)
      (fun z hz => show 0≤z.1 from hz.le)
  exact (hf _ ht.le).contDiffAt hn

lemma isOpen_retardedSpaceDomain (t : ℝ) (x : Vec) : IsOpen (retardedSpaceDomain t x) := by
  have h₁ : IsOpen {y : Vec | y≠x} := isOpen_ne
  have h₂ : IsOpen {y : Vec | 0<t-coneRadius x y} :=
    isOpen_lt continuous_const (continuous_const.sub ((continuous_const.sub continuous_id).norm))
  convert h₁.inter h₂ using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [retardedSpaceDomain,mem_ofPred_eq,mem_inter_iff,ne_comm]

lemma retarded_local_data {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ∃ K : Set Vec, IsCompact K ∧
      ContDiffOn ℝ 1 (retardedDensity s.f t x) (retardedSpaceDomain t x ×ˢ univ) ∧
      ∀ y ∈ retardedSpaceDomain t x, ∀ v ∉ K, retardedDensity s.f t x (y,v)=0 := by
  obtain ⟨K,hK,hz⟩ := hc t ht
  refine ⟨Prod.snd '' K,hK.image continuous_snd,?_,?_⟩
  · intro z hz
    exact (contDiffAt_retardedDensity
      (particle_contDiffAt_positive hf hz.1.2 z.1 z.2) hz.1.1).contDiffWithinAt
  · intro y hy v hv
    by_contra hne
    have htime : t-coneRadius x y ∈ Icc 0 t :=
      ⟨hy.2.le,sub_le_self _ (norm_nonneg _)⟩
    exact hv ⟨(y,v),hz _ htime (subset_tsupport _ hne),rfl⟩

lemma continuous_physicalElectricKernel_velocity {r : ℝ} {n : Vec}
    (hr : r≠0) (hn : ‖n‖=1) (E B : Vec) :
    Continuous (fun v => physicalElectricKernel r n (velocity v)
      (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hb : Continuous (fun v => fderiv ℝ velocity v (E+cross (velocity v) B)) :=
    ((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).clm_apply
      (contDiff_lorentz (k:=1) E B).continuous
  have hd : Continuous (fun v => 1-dot n (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hd0 (v : Vec) : 1-dot n (velocity v)≠0 := (cone_denom_pos v n hn).ne'
  have hnum : Continuous (fun v => 1-dot (velocity v) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hu.prodMk hu))
  have hnb : Continuous (fun v => dot n (fderiv ℝ velocity v (E+cross (velocity v) B))) :=
    (contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hb)
  exact ((hnum.div (continuous_const.mul (hd.pow 3)) (fun v => mul_ne_zero (pow_ne_zero 2 hr)
      (pow_ne_zero 3 (hd0 v)))).smul (continuous_const.sub hu)).add
    (((continuous_const.mul (hd.pow 3)).inv₀ (fun v => mul_ne_zero hr (pow_ne_zero 3 (hd0 v)))).smul
      ((hnb.smul (continuous_const.sub hu)).sub (hd.smul hb)))

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_integral_bound_compact {H W : Type*}
    [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {P : Set H} {K : Set Vec} {F : H × Vec → W}
    (hP : IsCompact P) (hK : IsCompact K)
    (hF : ContinuousOn F (P ×ˢ univ)) (hz : ∀ p ∈ P, ∀ v ∉ K, F (p,v)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ∈ P, ‖∫ v : Vec, F (p,v)‖≤C := by
  obtain ⟨C,hC⟩ := ((hP.prod hK).image_of_continuousOn (hF.mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩))).isBounded.exists_norm_le
  refine ⟨max C 0*volume.real K,mul_nonneg (le_max_right _ _) (measureReal_nonneg),?_⟩
  intro p hp
  have hc : Continuous (fun v : Vec => F (p,v)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v)) :=
    hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz p hp))
  have hfi : (∫ v : Vec, F (p,v))=∫ v in K, F (p,v) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hz p hp)
  rw [hfi]
  apply le_trans (norm_integral_le_integral_norm _)
  calc
    (∫ v in K, ‖F (p,v)‖) ≤ ∫ v in K, max C 0 := by
      apply integral_mono_ae hi.norm.integrableOn
        (integrableOn_const (hK.measure_lt_top.ne))
      filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
      exact le_trans (hC _ ⟨(p,v),⟨hp,hv⟩,rfl⟩) (le_max_left _ _)
    _ = max C 0*volume.real K := by simp [mul_comm]

lemma coneRadius_add (x z : Vec) : coneRadius x (x+z)=‖z‖ := by
  unfold coneRadius
  rw [show x-(x+z) = -z by abel,norm_neg]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma normalisedElectricKernel_eq {r : ℝ} (hr : r≠0) (n u b : Vec) :
    normalisedElectricKernel r n u b=r^2 • physicalElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,physicalElectricKernel,PiLp.add_apply,PiLp.smul_apply,
    PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma continuousOn_normalisedElectricKernel {H : Type*} [TopologicalSpace H]
    {r : H → ℝ} {n u b : H → Vec} {S : Set H}
    (hr : ContinuousOn r S) (hn : ContinuousOn n S) (hu : ContinuousOn u S)
    (hb : ContinuousOn b S) (hd : ∀ z ∈ S, 1-dot (n z) (u z)≠0) :
    ContinuousOn (fun z => normalisedElectricKernel (r z) (n z) (u z) (b z)) S := by
  have hdot (f g : H → Vec) (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun z => dot (f z) (g z)) S :=
    (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (hf.prodMk hg)
  have hD : ContinuousOn (fun z => 1-dot (n z) (u z)) S :=
    continuousOn_const.sub (hdot n u hn hu)
  have hp : ∀ z ∈ S, (1-dot (n z) (u z))^3≠0 := fun z hz => pow_ne_zero 3 (hd z hz)
  exact (((continuousOn_const.sub (hdot u u hu hu)).div (hD.pow 3) hp).smul (hn.sub hu)).add
    ((hr.div (hD.pow 3) hp).smul (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma field_contDiffAt_positive {k : ℕ∞ω} {F : Field}
    (hF : ContDiffOn ℝ k F fieldHalfSpace) {t : ℝ} (ht : 0<t) (x : Vec) :
    ContDiffAt ℝ k F (t,x) := by
  have hn : fieldHalfSpace ∈ 𝓝 (t,x) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)
      (fun p hp => show 0≤p.1 from hp.le)
  exact (hF _ ht.le).contDiffAt hn

lemma contDiffAt_physicalElectricKernel {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ∞ω} {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hr0 : r z≠0) (hd0 : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => physicalElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div ((hr.pow 2).mul (hD.pow 3))
      (mul_ne_zero (pow_ne_zero 2 hr0) (pow_ne_zero 3 hd0))).smul (hn.sub hu)).add
    (((hr.mul (hD.pow 3)).inv (mul_ne_zero hr0 (pow_ne_zero 3 hd0))).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma contDiffAt_retardedElectricIntegrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} {x y v : Vec} (hxy : x≠y) (ht : 0<t-coneRadius x y) :
    ContDiffAt ℝ 1 (fun z : Phase =>
      (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
        physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
          (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+
            cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))))) (y,v) := by
  have hr : ContDiffAt ℝ 1 (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ 1 (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have harg : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius x z.1,z.1)) (y,v) :=
    (contDiffAt_const.sub hr).prodMk contDiffAt_fst
  have he := (field_contDiffAt_positive hE ht y).comp (y,v) harg
  have hm := (field_contDiffAt_positive hB ht y).comp (y,v) harg
  have hcross : ContDiffAt ℝ 1 (fun z : Phase =>
      cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))) (y,v) :=
    contDiff_cross.contDiffAt.comp (y,v) (hu.prodMk hm)
  have hdf : ContDiff ℝ 1 (fderiv ℝ velocity) :=
    (contDiff_velocity (k:=2)).fderiv_right (by norm_num)
  have hb : ContDiffAt ℝ 1 (fun z : Phase => fderiv ℝ velocity z.2
      (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))) (y,v) :=
    (hdf.contDiffAt.comp (y,v) contDiffAt_snd).clm_apply (he.add hcross)
  have hd0 : 1-dot (coneDirection x y) (velocity v)≠0 :=
    (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  have hk := contDiffAt_physicalElectricKernel hr hn hu hb
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) hd0
  exact ((contDiffAt_retardedDensity (particle_contDiffAt_positive hf ht y v) hxy).mul
    (contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu)))).smul hk

lemma contDiffOn_retardedElectricDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedElectricDensity s t x) (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,_,hz⟩ := retarded_local_data hf hc ht x
  unfold retardedElectricDensity
  apply contDiffOn_integral_uniform_support (n:=1)
    (F:=fun z : Phase => (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
      physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
        (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))))
    (isOpen_retardedSpaceDomain t x) hK
  · intro z hz
    exact (contDiffAt_retardedElectricIntegrand hf hE hB hz.1.1 hz.1.2).contDiffWithinAt
  · intro y hy v hv
    change (retardedDensity s.f t x (y,v)*_) • _=0
    rw [hz y hy v hv,zero_mul,zero_smul]

lemma integrableOn_ball_of_punctured_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {R C α : ℝ} (hα : α<3)
    (hF : ContinuousOn F (ball (0:Vec) R \ {0}))
    (hb : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → ‖F z‖≤C*‖z‖^(-α)) :
    IntegrableOn F (ball (0:Vec) R) := by
  have hae : (ball (0:Vec) R \ ({0} : Set Vec) : Set Vec) =ᵐ[volume] (ball (0:Vec) R : Set Vec) := by
    filter_upwards [volume.ae_ne (0:Vec)] with z hz
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩
  have hmeas : AEStronglyMeasurable F (volume.restrict (ball (0:Vec) R)) := by
    rw [← Measure.restrict_congr_set hae]
    exact hF.aestronglyMeasurable (measurableSet_ball.diff (measurableSet_singleton _))
  apply ((integrableOn_norm_rpow_neg hα).const_mul C).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hb z (norm_pos_iff.mpr hz0) (by simpa only [mem_ball_zero_iff] using hz)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CrossCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma crossCLM_apply (n v : Vec) : crossCLM n v=cross n v := rfl

lemma integral_cross_left {F : Vec → Vec} (hF : Integrable F) (n : Vec) :
    (∫ v : Vec, cross n (F v))=cross n (∫ v : Vec, F v) :=
  (crossCLM n).integral_comp_comm hF

lemma integrable_retardedElectricDensity_integrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) :
    Integrable (fun v : Vec =>
      (s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))) •
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) := by
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht y
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  exact ((hreg.continuous.mul hd).smul hk).integrable_of_hasCompactSupport (hcomp.mul_right.smul_right)

lemma retardedMagneticDensity_component {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    retardedMagneticDensity s t x y i =
    ∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
      cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) i := by
  have hi := integrable_retardedElectricDensity_integrand hf hc hxy ht
  have hcross := (crossCLM (coneDirection x y)).integrable_comp hi
  unfold retardedMagneticDensity retardedElectricDensity
  rw [← integral_cross_left hi]
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hcross
  simpa only [crossCLM_apply,PiLp.proj_apply,cross_smul_right,PiLp.smul_apply,smul_eq_mul] using he.symm

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_MagneticMomentDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffOn_retardedMagneticDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedMagneticDensity s t x) (retardedSpaceDomain t x) := by
  intro y hy
  have hn : ContDiffAt ℝ 1 (coneDirection x) y := contDiffAt_coneDirection hy.1
  exact (contDiff_cross.contDiffAt.comp y (hn.prodMk
    ((contDiffOn_retardedElectricDensity hf hE hB hc ht x).contDiffAt
      ((isOpen_retardedSpaceDomain t x).mem_nhds hy)))).contDiffWithinAt

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedWeightedIntegralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma retarded_weighted_integral_bound_le {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, ‖z‖≤R → ∀ n : Vec, ‖n‖=1 →
      ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) • A ((z,n),v)‖≤C := by
  have ht : 0≤t := le_trans hR hRt
  obtain ⟨K,hK,hz⟩ := hc t ht
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  have hzero : ∀ p ∈ P, ∀ v ∉ Prod.snd '' K, s.f (t-‖p.1‖,x+p.1,v) • A (p,v)=0 := by
    intro p hp v hv
    have hsf : s.f (t-‖p.1‖,x+p.1,v)=0 := by
      by_contra hne
      exact hv ⟨(x+p.1,v),hz _ (htime p.1 hp.1) (subset_tsupport _ hne),rfl⟩
    rw [hsf,zero_smul]
  obtain ⟨C,hC,hb⟩ := uniform_integral_bound_compact hP (hK.image continuous_snd) (hcf.smul hA) hzero
  refine ⟨C,hC,?_⟩
  intro z hz n hn
  exact hb (z,n) ⟨by simpa only [mem_closedBall_zero_iff] using hz,
    by simpa only [mem_sphere,dist_zero_right] using hn⟩

lemma retarded_electric_kernel_norm_bound_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖∫ v : Vec, (s.f (t-coneRadius x (x+z),x+z,v)*
        (1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel (coneRadius x (x+z)) (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x (x+z),x+z)+
            cross (velocity v) (s.B (t-coneRadius x (x+z),x+z))))‖≤C/‖z‖^2 := by
  let S : Set ((Vec × Vec) × Vec) := (closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ
  let u : (Vec × Vec) × Vec → Vec := fun p => velocity p.2
  let n : (Vec × Vec) × Vec → Vec := fun p => p.1.2
  let b : (Vec × Vec) × Vec → Vec := fun p => fderiv ℝ velocity p.2
    (s.E (t-‖p.1.1‖,x+p.1.1)+cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1)))
  have hu : Continuous u := (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hn : Continuous n := continuous_fst.snd
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk (continuous_const.add continuous_fst.fst)
  have hmap : MapsTo (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) S fieldHalfSpace := by
    intro p hp
    have hnz : ‖p.1.1‖≤R := by simpa only [mem_closedBall_zero_iff] using hp.1.1
    change 0≤t-‖p.1.1‖
    linarith
  have he := hE.comp harg.continuousOn hmap
  have hm := hB.comp harg.continuousOn hmap
  have hcross : ContinuousOn (fun p : (Vec × Vec) × Vec =>
      cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1))) S :=
    (contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hm)
  have hb : ContinuousOn b S :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp continuous_snd).continuousOn.clm_apply (he.add hcross)
  have hD : Continuous (fun p : (Vec × Vec) × Vec => 1-dot (n p) (u p)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hD0 (p : (Vec × Vec) × Vec) (hp : p ∈ S) : 1-dot (n p) (u p)≠0 := by
    apply (cone_denom_pos _ _ ?_).ne'
    simpa only [n,mem_sphere,dist_zero_right] using hp.1.2
  have hN := continuousOn_normalisedElectricKernel (S:=S)
    continuous_fst.fst.norm.continuousOn hn.continuousOn hu.continuousOn hb hD0
  obtain ⟨C,hC,hbound⟩ := retarded_weighted_integral_bound_le hf hc hR hRt x (hD.continuousOn.smul hN)
  refine ⟨C,hC,?_⟩
  intro z hz0 hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz0)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have hh := hbound z hzR (coneDirection x (x+z)) (coneDirection_norm hxy)
  have heq : (∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))) =
      ‖z‖^2 • ∫ v : Vec, (s.f (t-‖z‖,x+z,v)*(1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [normalisedElectricKernel_eq hz0.ne']
    simp only [smul_smul]
    congr 1
    ring
  change ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))‖≤C at hh
  rw [heq,norm_smul,Real.norm_of_nonneg (sq_nonneg _)] at hh
  simp only [coneRadius_add]
  apply (le_div_iff₀ (sq_pos_of_pos hz0)).mpr
  simpa only [mul_comm] using hh

lemma integrableOn_retardedMagneticDensity_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont := (contDiffOn_retardedMagneticDensity hf hE hB hc ht x).continuousOn.comp
    (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound_le hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=C) (by norm_num) hcont
  intro z hz hzR
  have hxy : x≠x+z := (hm ⟨by simpa only [mem_ball_zero_iff] using hzR,by simpa only [mem_singleton_iff] using norm_pos_iff.mp hz⟩).1
  calc
    ‖retardedMagneticDensity s t x (x+z)‖ ≤ ‖coneDirection x (x+z)‖*‖retardedElectricDensity s t x (x+z)‖ := norm_cross_le _ _
    _ = ‖retardedElectricDensity s t x (x+z)‖ := by rw [coneDirection_norm hxy,one_mul]
    _ ≤ C/‖z‖^2 := hbound z hz hzR.le
    _ = C*‖z‖^(-(2:ℝ)) := by rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]; rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ContinuousIntegralSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma continuousOn_integral_sphere {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {S : Set H} {F : H × Vec → W}
    (hF : ContinuousOn F (S ×ˢ sphere (0:Vec) 1)) :
    ContinuousOn (fun p => ∫ n : Sphere, F (p,n.1) ∂sphereMeasure) S := by
  have hc : ContinuousOn (fun p : H × Sphere => F (p.1,p.2.1)) (S ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1,p.2.2⟩)
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc
  intro p n _ hn
  exact (hn (mem_univ n)).elim

lemma integral_ball_radius_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t : ℝ} (ht : 0<t) (hF : IntegrableOn F (ball (0:Vec) t)) :
    Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) (t-a), F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t, F z)) := by
  have hh : Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) t,
      (ball (0:Vec) (t-a)).indicator F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t, F z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    · exact Eventually.of_forall (fun a => hF.aestronglyMeasurable.indicator measurableSet_ball)
    · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => norm_indicator_le_norm_self _ _))
    · exact hF.norm
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hn : ‖z‖<t := by simpa only [mem_ball_zero_iff] using hz
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (show 0<t-‖z‖ by linarith)] with a ha
      symm
      apply indicator_of_mem
      simpa only [mem_ball_zero_iff] using (show ‖z‖<t-a by linarith [ha.2])
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  rw [setIntegral_indicator measurableSet_ball,inter_eq_right.mpr (ball_subset_ball (by linarith [ha.1]))]

lemma freeWave_sphere {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (r : ℝ) (x : Vec) :
    freeWave g h (r,x) = (4*Real.pi)⁻¹ *
      ((∫ n : Sphere, g (x+r • n.1) ∂sphereMeasure) +
        r*(∫ n : Sphere, fderiv ℝ g (x+r • n.1) n.1 ∂sphereMeasure)) +
      (4*Real.pi)⁻¹ * (r*∫ n : Sphere, h (x+r • n.1) ∂sphereMeasure) := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp))]
  have hd := ((hasDerivAt_id r).mul (sphereSum_radial_deriv (hg.of_le (by simp)) x r)).const_mul ((4*Real.pi)⁻¹)
  change HasDerivAt (fun t => waveK g (t,x)) _ r at hd
  rw [hd.deriv]
  simp only [id_eq,one_mul,waveK,sphereSum]

lemma contDiff_slab_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × Vec → W} {k : ℕ∞ω} {T a : ℝ}
    (hF : ContDiffOn ℝ k F (Icc 0 T ×ˢ (univ : Set Vec))) (ha : a ∈ Icc 0 T) :
    ContDiff ℝ k (fun y => F (a,y)) := by
  apply contDiffOn_univ.mp
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ => ⟨ha,mem_univ y⟩)

lemma spatialPartial_spaceDerivative {F : Field} {T a : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 T ×ˢ (univ : Set Vec))) (ha : a ∈ Icc 0 T)
    (y : Vec) (i j : Fin 3) :
    spatialPartial (fun z => F (a,z) i) y j = spaceDerivative F (a,y) (basis j) i := by
  have h := hasFDerivAt_time_slice hF ha y
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y h
  change HasFDerivAt (fun z => F (a,z) i) _ y at hi
  rw [spatialPartial,hi.fderiv,spaceDerivative,h.fderiv]
  rfl

lemma continuousOn_slab_curl {F : Field} {T : ℝ} (hT : 0<T)
    (hF : ContDiffOn ℝ 2 F (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContinuousOn (fun p : ℝ × Vec => curl (fun y => F (p.1,y)) p.2)
      (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hc := (contDiffOn_spaceDerivative hT hF).continuousOn
  have hh (i j : Fin 3) : ContinuousOn
      (fun p : ℝ × Vec => spatialPartial (fun y => F (p.1,y) i) p.2 j)
      (Icc 0 T ×ˢ (univ : Set Vec)) := by
    have ht := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
      (hc.clm_apply (continuousOn_const (c:=basis j)))
    apply ht.congr
    intro p hp
    exact spatialPartial_spaceDerivative (hF.of_le (by decide)) hp.1 p.2 i j
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  fin_cases i <;> exact (hh _ _).sub (hh _ _)

lemma continuousOn_freeWave_slab {F : Field} {H : ℝ × Vec → ℝ} {T : ℝ} (hT : 0<T)
    (hF : ContDiffOn ℝ ∞ F (Icc 0 T ×ˢ (univ : Set Vec)))
    (hH : ContinuousOn H (Icc 0 T ×ˢ (univ : Set Vec))) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun a : ℝ => freeWave (fun y => F (a,y) i) (fun y => H (a,y)) (T-a,x))
      (Icc 0 T) := by
  let S : Set (ℝ × Vec) := Icc 0 T ×ˢ sphere (0:Vec) 1
  let A : ℝ × Vec → ℝ × Vec := fun p => (p.1,x+(T-p.1) • p.2)
  have hA : Continuous A := continuous_fst.prodMk
    (continuous_const.add ((continuous_const.sub continuous_fst).smul continuous_snd))
  have hmap : MapsTo A S (Icc 0 T ×ˢ (univ : Set Vec)) := fun p hp => ⟨hp.1,mem_univ _⟩
  have hval : ContinuousOn (fun p : ℝ × Vec => F (p.1,x+(T-p.1) • p.2) i) S :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
      (hF.continuousOn.comp hA.continuousOn hmap)
  have hder : ContinuousOn (fun p : ℝ × Vec => spaceDerivative F (p.1,x+(T-p.1) • p.2) p.2 i) S :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
      (((contDiffOn_spaceDerivative hT (hF.of_le (by decide))).continuousOn.comp hA.continuousOn hmap).clm_apply
        continuous_snd.continuousOn)
  have hH' := hH.comp hA.continuousOn hmap
  have hv := continuousOn_integral_sphere hval
  have hd := continuousOn_integral_sphere hder
  have hh := continuousOn_integral_sphere hH'
  have he := (hv.add (((continuousOn_const (c:=T)).sub continuousOn_id).mul hd)).const_mul ((4*Real.pi)⁻¹)
  have he' := he.add ((((continuousOn_const (c:=T)).sub continuousOn_id).mul hh).const_mul ((4*Real.pi)⁻¹))
  apply he'.congr
  intro a ha
  have hf := contDiff_component (contDiff_slab_slice hF ha) i
  dsimp only [A,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,id_eq,Function.comp_apply]
  rw [freeWave_sphere hf]
  congr 2
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with n
  have h := hasFDerivAt_time_slice (hF.of_le (by decide)) ha (x+(T-a) • n.1)
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp _ h
  change HasFDerivAt (fun y => F (a,y) i) _ (x+(T-a) • n.1) at hi
  rw [hi.fderiv,spaceDerivative,h.fderiv]
  rfl

lemma coneBoundary_radius {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : coneRadius x (x+(T-a) • n)=T-a := by
  rw [coneRadius_add,norm_smul,Real.norm_of_nonneg (by linarith [ha.2]),
    show ‖n‖=1 by simpa only [mem_sphere,dist_zero_right] using hn,mul_one]

lemma coneBoundary_ne {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : x≠x+(T-a) • n := by
  intro he
  have hh := coneBoundary_radius hT ha hn x
  rw [← he,coneRadius,sub_self,norm_zero] at hh
  linarith [ha.2]

lemma continuousOn_weighted_cone_boundary {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {T : ℝ} (hT : 0<T) (x : Vec) {w : Phase → W}
    (hw : ∀ z : Phase, x≠z.1 → ContinuousAt w z) :
    ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, s.f (p.1,x+(T-p.1) • p.2,v) •
      w (x+(T-p.1) • p.2,v)) (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  obtain ⟨K,hK,hz⟩ := hc T hT.le
  let S : Set (ℝ × Vec) := Icc 0 (T/2) ×ˢ sphere (0:Vec) 1
  have harg : Continuous (fun p : (ℝ × Vec) × Vec => (p.1.1,x+(T-p.1.1) • p.1.2,p.2)) :=
    continuous_fst.fst.prodMk ((continuous_const.add
      ((continuous_const.sub continuous_fst.fst).smul continuous_fst.snd)).prodMk continuous_snd)
  have hcf := hf.continuousOn.comp harg.continuousOn (show MapsTo _ (S ×ˢ univ) particleHalfSpace from
    fun p hp => hp.1.1.1)
  have hwc : ContinuousOn (fun p : (ℝ × Vec) × Vec => w (x+(T-p.1.1) • p.1.2,p.2)) (S ×ˢ univ) := by
    intro p hp
    exact ((hw _ (coneBoundary_ne hT hp.1.1 hp.1.2 x)).comp
      (harg.snd.continuousAt)).continuousWithinAt
  apply continuousOn_integral_uniform_support (hK.image continuous_snd) (hcf.smul hwc)
  intro p hp v hv
  have ht : p.1 ∈ Icc 0 T := ⟨hp.1.1,by linarith [hp.1.2]⟩
  have hfz : s.f (p.1,x+(T-p.1) • p.2,v)=0 := by
    by_contra hne
    exact hv ⟨(x+(T-p.1) • p.2,v),hz _ ht (subset_tsupport _ hne),rfl⟩
  change s.f (p.1,x+(T-p.1) • p.2,v) • w (x+(T-p.1) • p.2,v)=0
  rw [hfz,zero_smul]

lemma continuousOn_magnetic_flux_boundary {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun p : ℝ × Vec => retardedMagneticFlux s T x i (x+(T-p.1) • p.2))
      (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  have hw (z : Phase) (hz : x≠z.1) : ContinuousAt (fun z : Phase => retardedH x z i • velocity z.2) z :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp
      (contDiffAt_retardedH (k:=1) hz).continuousAt).smul
      ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousAt
  apply (continuousOn_weighted_cone_boundary hf hc hT x hw).congr
  intro p hp
  unfold retardedMagneticFlux retardedDensity
  dsimp only
  rw [coneBoundary_radius hT hp.1 hp.2 x,sub_sub_cancel]
  congr 1
  funext v
  simp only [smul_smul]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ElectricConeBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma tendsto_right_of_continuousOn_Icc {W : Type*} [TopologicalSpace W]
    {F : ℝ → W} {R : ℝ} (hR : 0<R) (hF : ContinuousOn F (Icc 0 R)) :
    Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (F 0)) := by
  apply (hF 0 ⟨le_rfl,hR.le⟩).mono_left
  apply le_inf nhdsWithin_le_nhds
  apply Filter.le_principal_iff.mpr
  filter_upwards [Ioo_mem_nhdsGT hR] with a ha
  exact ⟨ha.1.le,ha.2.le⟩

lemma RegularParticle.current_continuous_slab {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0≤T) : ContinuousOn (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2)
      (Icc 0 T ×ˢ (univ : Set Vec)) :=
  hf.moment_continuous_slab (contDiff_velocity (k:=1)).continuous hT

lemma continuousOn_cone_boundary_comp {W : Type*} [TopologicalSpace W] {H : ℝ × Vec → W}
    {T : ℝ} (hT : 0<T) (hH : ContinuousOn H (Icc 0 T ×ˢ (univ : Set Vec))) (x : Vec) :
    ContinuousOn (fun p : ℝ × Vec => H (p.1,x+(T-p.1) • p.2))
      (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  apply hH.comp (continuous_fst.prodMk
    (continuous_const.add ((continuous_const.sub continuous_fst).smul continuous_snd))).continuousOn
  intro p hp
  exact ⟨⟨hp.1.1,by linarith [hp.1.2]⟩,mem_univ _⟩

end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ElectricBoundaryField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma cross_add_right (a b c : Vec) : cross a (b+c)=cross a b+cross a c :=
  (crossCLM a).map_add b c

lemma magneticConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedMagneticFlux s t x i (x+t • n.1)=
      retardedMagneticFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedMagneticFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold magneticConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [current,hf]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_BranchIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma norm_coordinate_le (v : Vec) (i : Fin 3) : |v i|≤‖v‖ := by
  exact (PiLp.norm_apply_le v i)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_EquationsBefore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma ClassicalBefore.regularParticle {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) : RegularParticle s.f := ⟨hs.1,hs.2.2.2.2.2.2.1⟩

lemma continuousOn_magneticConeBoundary_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (magneticConeBoundary s T x i) (Icc 0 (T/2)) := by
  have hc := hs.2.2.2.2.2.2.1
  have hE : ContDiffOn ℝ ∞ s.E (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.1.mono (fun p hp => hp.1)
  have hB : ContDiffOn ℝ ∞ s.B (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.2.mono (fun p hp => hp.1)
  have hcurl := ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
    (continuousOn_slab_curl hT (hE.of_le (by decide)))).neg
  have hfree := (continuousOn_freeWave_slab hT hB hcurl x i).mono
    (show Icc 0 (T/2) ⊆ Icc 0 T from fun a ha => ⟨ha.1,by linarith [ha.2]⟩)
  have hflux := continuousOn_magnetic_flux_boundary hs.1 hc hT x i
  have hdot := (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hflux)
  have hflux' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).pow 2).mul hdot)
  have hj := continuousOn_cone_boundary_comp hT (hs.regularParticle.current_continuous_slab hT.le) x
  have hterm (j k : Fin 3) := (((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).mul
    (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp continuous_snd).continuousOn)).mul
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).continuous.comp_continuousOn hj)
  have hj' := continuousOn_integral_sphere ((hterm (curlA i) (curlB i)).sub (hterm (curlB i) (curlA i)))
  exact (hfree.sub (hflux'.const_mul ((4*Real.pi)⁻¹))).add (hj'.const_mul ((4*Real.pi)⁻¹))

lemma classical_magnetic_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (hH : T < H) (x : Vec) (i : Fin 3) :
    s.B (T,x) i = magneticConeBoundary s T x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s T x (x+z) i) := by
  have hc := hs.2.2.2.2.2.2.1
  have hD : IntegrableOn (fun z => retardedMagneticDensity s T x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1 hc hT.le le_rfl x)
  have hlim := (tendsto_right_of_continuousOn_Icc (show 0<T/2 by linarith)
    (continuousOn_magneticConeBoundary_before hs hm hT x i)).add
    ((integral_ball_radius_tendsto hT hD).const_mul ((4*Real.pi)⁻¹))
  have heq : (fun a : ℝ => magneticConeBoundary s T x i a + (4*Real.pi)⁻¹ *
      (∫ z in ball (0:Vec) (T-a), retardedMagneticDensity s T x (x+z) i)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => s.B (T,x) i) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    have he := classical_shifted_magnetic_physical_representation_before hs hm ha.1
      (show 0<T-a by linarith [ha.2]) (by linarith) x i
    rw [show a+(T-a)=T by ring] at he
    unfold magneticConeBoundary
    linarith
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds |>.symm

lemma classical_magnetic_physical_vector_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x : Vec) :
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) := by
  have hD := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  ext i
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
  exact (classical_magnetic_physical_representation_before hs hm ht hH x i).trans
    (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
      smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

lemma classical_magneticConeBoundary_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary (datumBoundarySolution d) t x i 0 :=
  magneticConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_HomogeneousCancellation
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma physicalElectricKernel_eulerian_split {r : ℝ} {n u : Vec} (b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    (1-dot n u) • physicalElectricKernel r n u b =
      (r^2)⁻¹ • transportAngularCore n u+r⁻¹ • sourceAngularCore n u b := by
  ext i
  simp only [physicalElectricKernel,transportAngularCore,sourceAngularCore,
    PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma contDiffAt_transportAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => transportAngularCore (n w) (u w)) z := by
  have hdu := contDiff_dot_pair.contDiffAt.comp z (hu.prodMk hu)
  have hdn := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hu)
  exact ((contDiffAt_const.sub hdu).div ((contDiffAt_const.sub hdn).pow 2)
    (pow_ne_zero 2 hd)).smul (hn.sub hu)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_IntegralBallPolarFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma integral_ball_polar_flip {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec→W} {R : ℝ} (hg : IntegrableOn g (ball (0:Vec) R)) :
    (∫z in ball (0:Vec) R,g z)=
      ∫n : Sphere,∫r in Ioo (0:ℝ) R,r^2 • g (-(r • n.1)) ∂volume ∂sphereMeasure := by
  classical
  let H := (ball (0:Vec) R).indicator g
  have hi : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr hg
  rw [←integral_indicator measurableSet_ball]
  change (∫z,H z)=_
  rw [←integral_neg_eq_self H volume,integral_polar hi.comp_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    have he : ∀r∈Ioi (0:ℝ),r^2 • H (-(r • n.1))=
        (Iio R).indicator (fun r=>r^2 • g (-(r • n.1))) r := by
      intro r hr
      have hnorm : ‖-(r • n.1)‖=r := by
        rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]
      by_cases h : r<R
      · rw [show H (-(r • n.1))=g (-(r • n.1)) from indicator_of_mem
          (show -(r • n.1)∈ball (0:Vec) R by simpa only [mem_ball_zero_iff,hnorm] using h) g,
          indicator_of_mem (show r∈Iio R from h)]
      · rw [show H (-(r • n.1))=0 from indicator_of_notMem
          (show -(r • n.1)∉ball (0:Vec) R by simpa only [mem_ball_zero_iff,hnorm] using h) g,
          smul_zero,indicator_of_notMem (show r∉Iio R from h)]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Iio]
    rfl)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_Icc_sub (H : ℝ → ℝ) {t : ℝ} (ht : 0≤t) :
    (∫ r in Icc (0:ℝ) t, H (t-r))=∫ r in Icc (0:ℝ) t, H r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht,← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left]
  simp only [sub_self,sub_zero]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_TransportAngularCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma physicalMagneticKernel_eulerian_split {r : ℝ} {n u : Vec} (b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    (1-dot n u) • cross n (physicalElectricKernel r n u b) =
      (r^2)⁻¹ • transportAngularCore n u+r⁻¹ • sourceAngularCore n u b := by
  have hh := congrArg (cross n) (RVM.physicalElectricKernel_eulerian_split b hr hd)
  simpa only [cross_smul_right,cross_add_right,transportAngularCore,sourceAngularCore] using hh

lemma contDiffAt_transportAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => transportAngularCore (n w) (u w)) z := by
  exact contDiff_cross.contDiffAt.comp z (hn.prodMk (RVM.contDiffAt_transportAngularCore hn hu hd))

lemma transportConeCoefficient_contDiffAt (i : Fin 3) {p : Phase} (hp : p.1≠0) :
    ContDiffAt ℝ 1 (transportConeCoefficient i) p := by
  have hz : (0:Vec)≠p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hA := contDiffAt_transportAngularCore hn hu (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact ((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi

attribute [local instance] Measure.Subtype.measureSpace

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffAt_sourceAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u b : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z) (hb : ContDiffAt ℝ k b z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => sourceAngularCore (n w) (u w) (b w)) z := by
  have hnb := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hb)
  have hnu := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hu)
  exact (((contDiffAt_const.sub hnu).pow 2).inv (pow_ne_zero 2 hd)).smul
    ((hnb.smul (hn.sub hu)).sub ((contDiffAt_const.sub hnu).smul hb))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma contDiffAt_sourceAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u b : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z) (hb : ContDiffAt ℝ k b z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => sourceAngularCore (n w) (u w) (b w)) z := by
  exact contDiff_cross.contDiffAt.comp z (hn.prodMk (RVM.contDiffAt_sourceAngularCore hn hu hb hd))

lemma sourceAngularProfile_contDiffAt (i : Fin 3) {p : (Vec × Vec × Vec) × Vec}
    (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (sourceAngularProfile i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  have hdv : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => fderiv ℝ velocity z.2) p :=
    ((contDiff_velocity (k:=2)).fderiv_right (by norm_num)).contDiffAt.comp p contDiffAt_snd
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p
    (contDiffAt_sourceAngularCore hn hu (hdv.clm_apply hforce) hd)

lemma sourceConeCoefficient_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) (i : Fin 3) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (sourceConeCoefficient s t x i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hp.symm).comp p contDiffAt_fst
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 p.1,
      s.E (t-coneRadius 0 p.1,x+p.1),s.B (t-coneRadius 0 p.1,x+p.1)),p.2))
    (cone_denom_pos p.2 _ (coneDirection_norm hp.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))).mul hc

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_TransportSingularBulk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma shifted_particle_continuousOn {f : Particle} {t U : ℝ} (x : Vec) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    ContinuousOn (fun p : Phase => f (t-coneRadius 0 p.1,x+p.1,p.2))
      (retardedSpaceDomain t 0 ×ˢ univ) := by
  apply hf.comp (by unfold coneRadius; fun_prop : Continuous
    (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2))).continuousOn
  intro p hp
  exact ⟨hp.1.2.le,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-p.1)]⟩

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalC0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma kernel_volterra_norm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Vec → W} {t C : ℝ} (ht : 0≤t) (_ : 0≤C)
    (hF : IntegrableOn F (ball (0:Vec) t)) {g : ℝ → ℝ} (hg : Continuous g)
    (hb : ∀ z, 0<‖z‖ → ‖z‖≤t → ‖F z‖≤C*g (t-‖z‖)/‖z‖^2) :
    ‖∫ z in ball (0:Vec) t, F z‖≤(4*Real.pi)*C*(∫ u in Icc (0:ℝ) t, g u) := by
  rw [integral_ball_polar_flip hF]
  have hr : IntegrableOn (fun r => C*g (t-r)) (Ioo (0:ℝ) t) :=
    ((continuous_const.mul (hg.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hin (a : Sphere) : ‖∫ r in Ioo (0:ℝ) t, r^2 • F (-(r • a.1))‖ ≤
      C*(∫ u in Icc (0:ℝ) t, g u) := by
    have hh := norm_integral_le_of_norm_le hr (f:=fun r => r^2 • F (-(r • a.1))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have he : ‖-(r • a.1)‖=r := by
        rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,sphere_norm,mul_one]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      have hh := hb (-(r • a.1)) (by simpa only [he] using hr.1) (by simpa only [he] using hr.2.le)
      rw [he] at hh
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg r)).trans_eq (by field_simp [ne_of_gt hr.1]))
    apply hh.trans_eq
    rw [←integral_Icc_eq_integral_Ioo,integral_const_mul,integral_Icc_sub g ht]
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (Filter.Eventually.of_forall hin)
  simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_VolterraKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma particle_spatial_fderiv {f : Particle} {u : ℝ} {y v : Vec}
    (hf : DifferentiableAt ℝ f (u,y,v)) (e : Vec) :
    fderiv ℝ (fun z => f (u,z,v)) y e=fderiv ℝ f (u,y,v) (0,e,0) := by
  have hm : HasFDerivAt (fun z : Vec => (u,z,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) y :=
    (hasFDerivAt_const u y).prodMk ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const v y))
  have hh := hf.hasFDerivAt.comp (f:=fun z : Vec => (u,z,v)) y hm
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma transportConeCoefficient_uniform_bound (P : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z v : Vec, z≠0 → ‖v‖≤P →
      |transportConeCoefficient i (z,v)|≤C/‖z‖^2 := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => transportAngularCore p.1 (velocity p.2) i) K := by
    intro p hp
    have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
    have hh := contDiffAt_transportAngularCore (k:=1) (z:=p) contDiffAt_fst
      (contDiff_velocity.contDiffAt.comp p contDiffAt_snd) (cone_denom_pos p.2 p.1 hn).ne'
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp hh.continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z v hz hv
  have hb := hC (coneDirection 0 z,v) ⟨by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩
  unfold transportConeCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (inv_nonneg.mpr (sq_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma transport_derivative_integrable {s : Solution} {U t P N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,transportConeCoefficient i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => transportConeCoefficient i p*
    fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0)
  let A := ball (0:Vec) t \ ({0} : Set Vec)
  have hzprop {z : Vec} (hz : z∈A) : z≠0 ∧ 0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hzr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact ⟨hz.2,by simpa [coneRadius] using sub_pos.mpr hzr,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-z)]⟩
  have hfc : ContinuousOn F (A ×ˢ univ) := by
    intro p hp
    have hh := hzprop hp.1
    have hr := (contDiffAt_coneRadius (k:=1) hh.1.symm).comp p contDiffAt_fst
    have hm : ContinuousAt (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2)) p :=
      ((contDiffAt_const.sub hr).prodMk ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd)).continuousAt
    have hdf : ContinuousAt (fun q : Phase => fderiv ℝ s.f (t-coneRadius 0 q.1,x+q.1,q.2)) p :=
      ((particle_contDiffAt_positive hf hh.2.1 (x+p.1) p.2).continuousAt_fderiv (by simp)).comp (f:=fun q : Phase => (t-coneRadius 0 q.1,x+q.1,q.2)) hm
    exact ((transportConeCoefficient_contDiffAt i hh.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖^2)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv))
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma particle_fixed_time_contDiff {s : Solution} {k : ℕ∞ω} {u : ℝ}
    (hf : ContDiffOn ℝ k s.f particleHalfSpace) (hu : 0≤u) :
    ContDiff ℝ k (fun p : Phase => s.f (u,p)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => hu)

lemma transport_kernel_velocity_contDiff (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiff ℝ 1 (fun v => transportConeCoefficient i (z,v)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  exact (transportConeCoefficient_contDiffAt i hz).comp v (contDiffAt_const.prodMk contDiffAt_id)

lemma hasDerivAt_transport_particle_line {s : Solution} {u P : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hu : 0<u)
    (hP : ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (x e z : Vec) (hz : z≠0) (i : Fin 3) (a : ℝ) :
    HasDerivAt (fun q : ℝ => ∫ v,transportConeCoefficient i (z,v)*s.f (u,x+q • e,v))
      (∫ v,transportConeCoefficient i (z,v)*fderiv ℝ s.f (u,x+a • e,v) (0,e,0)) a := by
  let F : ℝ × Vec → ℝ := fun p => s.f (u,x+p.1 • e,p.2)
  let w : Vec → ℝ := fun v => transportConeCoefficient i (z,v)
  have hF : ContDiff ℝ 1 F := (particle_fixed_time_contDiff hf hu.le).comp
    ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)
  have hw : ContDiff ℝ 1 w := transport_kernel_velocity_contDiff i hz
  have hzero (a : ℝ) (_ : a∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (a,v)=0 :=
    hP _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hG : ContDiffOn ℝ 1 (fun p : ℝ × Vec => w p.2*F p) (univ ×ˢ univ) :=
    ((hw.comp contDiff_snd).mul hF).contDiffOn
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG (by intro q hq v hv; rw [hzero q hq v hv,mul_zero])).differentiableAt.hasDerivAt
  rw [show deriv (fun x => ∫ v, w v*F (x,v)) a = fderiv ℝ (fun x => ∫ v,w v*F (x,v)) a 1 from rfl,fderiv_weighted_integral_uniform_support_apply isOpen_univ
    (isCompact_closedBall (0:Vec) P) (mem_univ a) hF.contDiffOn hw hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    apply congrArg (fun r : ℝ => w v*r)
    have hm : HasFDerivAt (fun p : ℝ × Vec => (u,x+p.1 • e,p.2))
        ((0 : (ℝ × Vec) →L[ℝ] ℝ).prod
          (((ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ Vec) e)).prod
            (ContinuousLinearMap.snd ℝ ℝ Vec))) (a,v) := by
      convert (hasFDerivAt_const u (a,v)).prodMk
        (((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
          (hasFDerivAt_snd (𝕜:=ℝ))) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | simp
    have hh := (particle_differentiableAt_positive hf hu _ v).hasFDerivAt.comp
      (f:=fun p : ℝ × Vec => (u,x+p.1 • e,p.2)) (a,v) hm
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      zero_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',one_smul,F,Function.comp_def] using
      congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv)

lemma norm_transport_velocity_integral_le {P C A : ℝ} {z : Vec} {i : Fin 3}
    {g : Vec → ℝ} (_hA : 0≤A)
    (hk : ∀ v, ‖v‖≤P → |transportConeCoefficient i (z,v)|≤C/‖z‖^2)
    (hzero : ∀ v, P<‖v‖ → g v=0) (hg : ∀ v, |g v|≤A) :
    ‖∫ v,transportConeCoefficient i (z,v)*g v‖≤volume.real (closedBall (0:Vec) P)*C*A/‖z‖^2 := by
  have heq : (∫ v,transportConeCoefficient i (z,v)*g v)=
      ∫ v in closedBall (0:Vec) P,transportConeCoefficient i (z,v)*g v := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),mul_zero]
  rw [heq]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => transportConeCoefficient i (z,v)*g v) (C:=(C/‖z‖^2)*A) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hk v (by simpa only [mem_closedBall,dist_zero_right] using hv)) (hg v)
        (abs_nonneg _) (le_trans (abs_nonneg _) (hk v (by simpa only [mem_closedBall,dist_zero_right] using hv))))
  exact hb.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ]; ring)

lemma transport_density_integrable {s : Solution} {U t P A : ℝ} (x : Vec) (i : Fin 3)
    (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) :
    IntegrableOn (fun z => ∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))
      (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => transportConeCoefficient i p*s.f (t-coneRadius 0 p.1,x+p.1,p.2)
  let U₀ := retardedSpaceDomain t 0
  have htime {z : Vec} (hz : z∈U₀) : t-coneRadius 0 z∈Icc (0:ℝ) U :=
    ⟨hz.2.le,(sub_le_self _ (norm_nonneg _)).trans htU⟩
  have hk : ContinuousOn (transportConeCoefficient i) (U₀ ×ˢ univ) := by
    intro p hp
    exact (transportConeCoefficient_contDiffAt i hp.1.1.symm).continuousAt.continuousWithinAt
  have hfc : ContinuousOn F (U₀ ×ˢ univ) := hk.mul
      (shifted_particle_continuousOn x htU (hf.continuousOn.mono (fun p hp => hp.1)))
  have hzero (z : Vec) (hz : z∈U₀) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    dsimp [F]
    rw [hP _ (htime hz) _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),mul_zero]
  have hsub : ball (0:Vec) t \ ({0} : Set Vec)⊆U₀ := by
    intro z hz
    exact ⟨(show z≠0 from hz.2).symm,by simpa only [coneRadius,zero_sub,norm_neg] using
      (sub_pos.mpr (show ‖z‖<t by simpa only [mem_ball,dist_zero_right] using hz.1))⟩
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=volume.real (closedBall (0:Vec) P)*C*A)
    (by norm_num) ((continuousOn_integral_uniform_support (isCompact_closedBall _ _) hfc hzero).mono hsub)
  intro z hz hzt
  have hzu : z∈U₀ := hsub ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hb := norm_transport_velocity_integral_le hA (fun v hv => hcb z v (norm_pos_iff.mp hz) hv)
    (hP _ (htime hzu) (x+z)) (hfA _ (htime hzu) (x+z))
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_two,div_eq_mul_inv] using hb

lemma hasDerivAt_magnetic_transport_integral {s : Solution} {U t P A N : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ)
    (ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hA : 0≤A) (hN : 0≤N)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
      transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t, ∫ v,transportConeCoefficient i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,(x+a • e)+z,v) (0,e,0)) a := by
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have htime {z : Vec} (hz : z∈ball (0:Vec) t) :
      0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    exact ⟨by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hr,
      (sub_le_self _ (norm_nonneg _)).trans htU⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => D*‖z‖^(-(2:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (transport_density_integrable (x+q • e) i htU hf hA hP hfA).aestronglyMeasurable))
    (transport_density_integrable (x+a • e) i htU hf hA hP hfA)
    (transport_derivative_integrable (x+a • e) e i ht htU hf hN hP hfN).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (2:ℝ)<3 by norm_num)).const_mul D) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    intro q _
    have htz := htime hz
    refine (norm_transport_velocity_integral_le (mul_nonneg hN (norm_nonneg e))
      (fun v hv => hcb z v hz0 hv) ?_ ?_).trans_eq ?_
    · intro v hv
      rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf htz.1 _ _) e]
      have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
        funext (fun y => hP _ ⟨htz.1.le,htz.2⟩ y v hv)
      rw [he]
      simp
    · intro v
      rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf htz.1 _ _) e]
      simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans
        (mul_le_mul_of_nonneg_right (hfN _ ⟨htz.1.le,htz.2⟩ _ v) (norm_nonneg e))
    · simp only [D,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
      ring
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    intro q _
    have htz := htime hz
    simpa only [add_right_comm] using hasDerivAt_transport_particle_line hf htz.1
      (hP _ ⟨htz.1.le,htz.2⟩) (x+z) e z hz0 i q

lemma sourceConeCoefficient_uniform_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |sourceConeCoefficient s t x i (z,v)|≤C/‖z‖ := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (sourceAngularProfile i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact (sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s t x z v hz hv hE hB
  have hb := hC ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v) (by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
    · simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB
    · simpa only [mem_closedBall,dist_zero_right] using hv)
  unfold sourceConeCoefficient sourceFixedCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _))
    (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma source_particle_derivative_integrable {s : Solution} {U t P M N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => sourceConeCoefficient s t x i p*
    fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0)
  let A := ball (0:Vec) t \ ({0} : Set Vec)
  have hzprop {z : Vec} (hz : z∈A) : z≠0 ∧ 0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hzr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact ⟨hz.2,by simpa [coneRadius] using sub_pos.mpr hzr,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-z)]⟩
  have hfc : ContinuousOn F (A ×ˢ univ) := by
    intro p hp
    have hh := hzprop hp.1
    have hr := (contDiffAt_coneRadius (k:=1) hh.1.symm).comp p contDiffAt_fst
    have hm : ContinuousAt (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2)) p :=
      ((contDiffAt_const.sub hr).prodMk ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd)).continuousAt
    have hdf : ContinuousAt (fun q : Phase => fderiv ℝ s.f (t-coneRadius 0 q.1,x+q.1,q.2)) p :=
      ((particle_contDiffAt_positive hf hh.2.1 (x+p.1) p.2).continuousAt_fderiv (by simp)).comp (f:=fun q : Phase => (t-coneRadius 0 q.1,x+q.1,q.2)) hm
    exact ((sourceConeCoefficient_contDiffAt hE hB x i hh.1 hh.2.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := sourceConeCoefficient_uniform_bound P M i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_one]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb s t x z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv)
        (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).1 (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).2)
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma sourceAngularProfile_derivative_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖fderiv ℝ (sourceAngularProfile i) ((n.1,E,B),v)‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fderiv ℝ (sourceAngularProfile i)) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact ((sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

lemma sourceReceiverKernel_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceReceiverKernel s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hn := (contDiffAt_coneDirection (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_fst.add contDiffAt_snd.fst)
  have he := (field_contDiffAt_positive hE ht (p.1+p.2.1)).comp p hm
  have hb := (field_contDiffAt_positive hB ht (p.1+p.2.1)).comp p hm
  have hprof := (sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 p.2.1,s.E (t-coneRadius 0 p.2.1,p.1+p.2.1),s.B (t-coneRadius 0 p.2.1,p.1+p.2.1)),p.2.2))
    (cone_denom_pos p.2.2 _ (coneDirection_norm hz.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd.snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hprof

lemma source_receiver_fderiv_formula {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e =
      (coneRadius 0 z)⁻¹*fderiv ℝ (sourceAngularProfile i)
        ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v)
        ((0,fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),0) := by
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk ((hasFDerivAt_id (𝕜:=ℝ) x).add_const z)
  have he := ((field_contDiffAt_positive hE ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hb := ((field_contDiffAt_positive hB ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hp := ((sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).hasFDerivAt.comp x
      (((hasFDerivAt_const (coneDirection 0 z) x).prodMk (he.prodMk hb)).prodMk (hasFDerivAt_const v x))
  have hh := hp.const_mul ((coneRadius 0 z)⁻¹)
  change HasFDerivAt (fun y => sourceConeCoefficient s t y i (z,v)) _ x at hh
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma physical_source_receiver_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v e : Vec),
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      z≠0 → 0<t-coneRadius 0 z → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e|≤
        C/‖z‖*max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖
          ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖*‖e‖ := by
  obtain ⟨C,hC,hcb⟩ := sourceAngularProfile_derivative_bound P M i
  refine ⟨C,hC,?_⟩
  intro s t x z v e hE hB hz ht hv he hb
  rw [source_receiver_fderiv_formula x z v e i hE hB hz ht,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))]
  let Q := max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖
  have hQ : 0≤Q := (norm_nonneg _).trans (le_max_left _ _)
  have he' : ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_left ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ _) (norm_nonneg ((0:ℝ),e)))
  have hb' : ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_right _ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖) (norm_nonneg ((0:ℝ),e)))
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  have hd := hcb ⟨coneDirection 0 z,hn⟩ v _ _ hv he hb
  have harg : ‖(((0:Vec),fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),
      fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),(0:Vec))‖≤Q*‖e‖ := by
    simp only [Prod.norm_mk,norm_zero]
    exact max_le (max_le (by positivity) (max_le he' hb')) (by positivity)
  have hh := (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hd harg (norm_nonneg _) hC)
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg,Q]
  ring

lemma norm_velocity_integral_bound {P C : ℝ} {g : Vec → ℝ}
    (hzero : ∀ v, P<‖v‖ → g v=0) (hb : ∀ v, ‖v‖≤P → |g v|≤C) :
    ‖∫ v,g v‖≤volume.real (closedBall (0:Vec) P)*C := by
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall (0:Vec) P)
    (f:=g) (fun v hv => hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv))]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P)) (f:=g) (C:=C) (by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
    simpa only [Real.norm_eq_abs] using hb v (by simpa only [mem_closedBall,dist_zero_right] using hv))
  simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

lemma retarded_packet_integrable {F : Vec × Phase → ℝ} {t P C : ℝ} (x : Vec)
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖) :
    IntegrableOn (fun z => ∫ v,F (x,z,v)) (ball (0:Vec) t) := by
  let A := ball (0:Vec) t \ ({0}:Set Vec)
  have hC : ContinuousOn (fun p : Phase => F (x,p)) (A ×ˢ univ) := by
    intro p hp
    exact ((hc (x,p) hp.1.2 (by simpa only [mem_ball,dist_zero_right] using hp.1.1)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzero (z : Vec) (hza : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (x,z,v)=0 :=
    hz x z v hza.2 (by simpa only [mem_ball,dist_zero_right] using hza.1)
      (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=volume.real (closedBall (0:Vec) P)*C)
    (by norm_num) (continuousOn_integral_uniform_support (isCompact_closedBall _ _) hC hzero)
  intro z hz0 hzt
  have hzn := norm_pos_iff.mp hz0
  have hh := norm_velocity_integral_bound (hz x z · hzn hzt) (hb x z · hzn hzt)
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh

lemma retarded_packet_spatial_fderiv {F : Vec × Phase → ℝ} {x z v : Vec}
    (hF : DifferentiableAt ℝ F (x,z,v)) (e : Vec) :
    fderiv ℝ (fun y => F (y,z,v)) x e=fderiv ℝ F (x,z,v) (e,0,0) := by
  have hh := hF.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma retarded_packet_derivative_zero {F : Vec × Phase → ℝ} {P t : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z v e : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) (hv : P<‖v‖) :
    fderiv ℝ F (x,z,v) (e,0,0)=0 := by
  rw [←retarded_packet_spatial_fderiv ((hF (x,z,v) hz0 hzt).differentiableAt (by simp)) e]
  have he : (fun y => F (y,z,v))=fun _ => (0:ℝ) := funext (fun y => hz y z v hz0 hzt hv)
  rw [he]
  simp

lemma hasDerivAt_retarded_packet_line {F : Vec × Phase → ℝ} {t P : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z e : Vec) (a : ℝ) (hz0 : z≠0) (hzt : ‖z‖<t) :
    HasDerivAt (fun q : ℝ => ∫ v,F (x+q • e,z,v))
      (∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let G : ℝ × Vec → ℝ := fun p => F (x+p.1 • e,z,p.2)
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hF (x+p.1 • e,z,p.2) hz0 hzt).comp p
      ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk
        (contDiffAt_const.prodMk contDiffAt_snd))
  have hzero (q : ℝ) (_ : q∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : G (q,v)=0 :=
    hz _ z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG.contDiffOn hzero).differentiableAt.hasDerivAt
  rw [show deriv (fun q => ∫ v,G (q,v)) a = fderiv ℝ (fun q => ∫ v,G (q,v)) a 1 from rfl,
    fderiv_integral_uniform_support_apply isOpen_univ (isCompact_closedBall (0:Vec) P)
      (mem_univ a) hG.contDiffOn hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  apply ae_of_all
  intro v
  have hm := ((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
    ((hasFDerivAt_const z (a,v)).prodMk (hasFDerivAt_snd (𝕜:=ℝ)))
  have hh := ((hF (x+a • e,z,v) hz0 hzt).differentiableAt (by simp)).hasFDerivAt.comp (a,v) hm
  change HasFDerivAt G _ (a,v) at hh
  simpa using congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv

lemma hasDerivAt_retarded_packet_integral {F : Vec × Phase → ℝ} {t P C D : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖)
    (x e : Vec) (a : ℝ)
    (hD : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |fderiv ℝ F (x,z,v) (e,0,0)|≤D/‖z‖) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,F (x+q • e,z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let V := volume.real (closedBall (0:Vec) P)
  have hfc := fun p hp ht => (hF p hp ht).continuousAt
  have hdc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t →
      ContinuousAt (fun p => fderiv ℝ F p (e,0,0)) p := by
    intro p hp ht
    exact ((hF p hp ht).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hdz := fun x z v hz0 hzt hv => retarded_packet_derivative_zero hF hz x z v e hz0 hzt hv
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => V*D*‖z‖^(-(1:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (retarded_packet_integrable (x+q • e) hfc hz hb).aestronglyMeasurable))
    (retarded_packet_integrable (x+a • e) hfc hz hb)
    (retarded_packet_integrable (x+a • e) hdc hdz hD).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (1:ℝ)<3 by norm_num)).const_mul (V*D)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hzball
    have hh := norm_velocity_integral_bound (hdz (x+q • e) z · hz0 hzt) (hD (x+q • e) z · hz0 hzt)
    simpa only [V,Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    exact hasDerivAt_retarded_packet_line hF hz x z e q hz0 (by simpa only [mem_ball,dist_zero_right] using hzball)

end RVM.Magnetic

namespace RVM

lemma radial_volterra_majorant_integrable {t C : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn (fun z : Vec => C*g (t-‖z‖)/‖z‖^2) (ball (0:Vec) t) := by
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:Vec) t).exists_bound_of_continuousOn
    (f:=fun z : Vec => C*g (t-‖z‖)) (by fun_prop)
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=D) (by norm_num)
  · intro z hz
    have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz.2
    exact ((continuous_const.mul (hg.comp (continuous_const.sub continuous_norm))).continuousAt.div
      (continuous_norm.pow 2).continuousAt (pow_ne_zero 2 hn)).continuousWithinAt
  · intro z hz hzt
    rw [norm_div,norm_pow,norm_norm,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
    exact (div_le_div_of_nonneg_right (hD z (by
      simpa only [mem_closedBall,dist_zero_right] using hzt.le)) (sq_nonneg _)).trans_eq (by ring)

lemma kernel_volterra_norm_subset {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Vec → W} {t C : ℝ} {S : Set Vec}
    (ht : 0≤t) (hC : 0≤C) (hS : MeasurableSet S) (hsub : S⊆ball (0:Vec) t)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u∈Icc (0:ℝ) t,0≤g u)
    (hb : ∀ z∈S,z≠0 → ‖F z‖≤C*g (t-‖z‖)/‖z‖^2) :
    ‖∫ z in S,F z‖≤(4*Real.pi)*C*(∫ u in Icc (0:ℝ) t,g u) := by
  let G : Vec → ℝ := fun z => C*g (t-‖z‖)/‖z‖^2
  have hG : IntegrableOn G (ball (0:Vec) t) := radial_volterra_majorant_integrable hg
  have hgball (z : Vec) (hz : z∈ball (0:Vec) t) : 0≤g (t-‖z‖) :=
    hg0 _ ⟨by
      have hh : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
      exact sub_nonneg.mpr hh.le,
      sub_le_self _ (norm_nonneg z)⟩
  have hGb (z : Vec) (hz : z∈ball (0:Vec) t) : 0≤G z := by
    have hh := hgball z hz
    dsimp [G]; positivity
  have hh := norm_integral_le_of_norm_le (hG.mono_set hsub) (f:=F) (by
    filter_upwards [ae_restrict_mem hS,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact hb z hz hz0)
  apply hh.trans
  apply (setIntegral_mono_set hG (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hGb z hz) (ae_of_all _ (fun z hz => hsub hz))).trans
  apply (le_abs_self _).trans
  change ‖∫ z in ball (0:Vec) t,G z‖≤_
  apply kernel_volterra_norm ht hC hG hg
  intro z hz hzt
  dsimp [G]
  have hgzt := hg0 (t-‖z‖) ⟨sub_nonneg.mpr hzt,sub_le_self _ (norm_nonneg z)⟩
  rw [abs_of_nonneg (by positivity)]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SourceWeightedPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma sourceWeightedPacket_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p :=
    (contDiffAt_const.sub hr).prodMk ((contDiffAt_fst.add contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  exact (sourceReceiverKernel_contDiffAt i hE hB hz ht).mul
    ((particle_contDiffAt_positive hf ht (p.1+p.2.1) p.2.2).comp p hm)

lemma sourceWeightedPacket_fderiv {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)=
      fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)*s.f (t-coneRadius 0 z,x+z,v)+
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
  have hk := (sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  have hF := (sourceWeightedPacket_contDiffAt i hf hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  rw [←retarded_packet_spatial_fderiv hF e,←retarded_packet_spatial_fderiv hk e]
  have hkp := hk.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk
    (((hasFDerivAt_id (𝕜:=ℝ) x).add_const z).prodMk (hasFDerivAt_const v x))
  have hfp := (particle_differentiableAt_positive hf ht (x+z) v).hasFDerivAt.comp x hm
  have hh := hkp.mul hfp
  change HasFDerivAt (fun y => sourceWeightedPacket s t i (y,z,v)) _ x at hh
  change HasFDerivAt (fun y => sourceReceiverKernel s t i (y,z,v)) _ x at hkp
  rw [hh.fderiv,hkp.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    zero_apply,smul_eq_mul,Function.comp_apply,id_eq,sourceReceiverKernel]
  ring

lemma source_packet_estimates (P A M N Q : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (s : Solution) (U t : ℝ), t≤U →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceWeightedPacket s t i (x,z,v)|≤C/‖z‖ ∧
      |fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)|≤D/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  obtain ⟨L,hL,hlb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*A,L*Q*‖e‖*A+K*N*‖e‖,by positivity,by positivity,?_⟩
  intro s U t htU hf hE hB hfA hEB hDF hfN x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    have hr : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    rw [hr]
    constructor <;> linarith [norm_nonneg z]
  have hc := hkb s t x z v hz hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd := hlb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤L/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  have hfd : |fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤N*‖e‖ := by
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hu.1 _ _) e]
    exact (ContinuousLinearMap.le_opNorm _ e).trans
      (mul_le_mul_of_nonneg_right (hfN _ ⟨hu.1.le,hu.2⟩ _ v) (norm_nonneg e))
  constructor
  · change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul hc (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz hu.1]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact (add_le_add (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity))
      (mul_le_mul hc hfd (abs_nonneg _) (by positivity))).trans_eq (by ring)

lemma hasDerivAt_magnetic_source_integral {s : Solution} {U t P A M N Q : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ) (htU : t≤U)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hDF : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
      sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ (sourceWeightedPacket s t i) (x+a • e,z,v) (e,0,0)) a := by
  obtain ⟨C,D,hC,hD,hb⟩ := source_packet_estimates P A M N Q e i hA hN hQ
  have hbc := hb s U t htU hf hE hB hfA hEB hDF hfN
  apply hasDerivAt_retarded_packet_integral (F:=sourceWeightedPacket s t i) (P:=P) (C:=C) (D:=D) ?_ ?_
    (fun x z v hz hzt hv => (hbc x z v hz hzt hv).1) x e a (fun x z v hz hzt hv => (hbc x z v hz hzt hv).2)
  · intro p hp ht
    apply sourceWeightedPacket_contDiffAt i hf hE hB hp
    simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  · intro x z v hz hzt hv
    have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
      simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
      constructor <;> linarith [norm_nonneg z]
    simp only [sourceWeightedPacket,hP _ hu _ v hv,mul_zero]

lemma retarded_packet_inner_integrable {F : Vec × Phase → ℝ} {t P : ℝ}
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) : Integrable (fun v => F (x,z,v)) := by
  have hcont : Continuous (fun v => F (x,z,v)) := continuous_iff_continuousAt.mpr (fun v =>
    (hc (x,z,v) hz0 hzt).comp (f:=fun w : Vec => (x,z,w)) (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0:Vec) P)
    (fun v hv => hz x z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)))

lemma sourceReceiverParticlePacket_continuousAt {s : Solution} {t : ℝ} (e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : ‖p.2.1‖<t) :
    ContinuousAt (sourceReceiverParticlePacket s t e i) p := by
  have hu : 0<t-coneRadius 0 p.2.1 := by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  have hm : ContinuousAt (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p := (continuousAt_const.sub ((contDiffAt_coneRadius (k:=1) hz.symm).continuousAt.comp (f:=fun q : Vec × Phase => q.2.1) continuousAt_snd.fst)).prodMk
    ((continuousAt_fst.add continuousAt_snd.fst).prodMk continuousAt_snd.snd)
  exact (((sourceReceiverKernel_contDiffAt i hE hB hz hu).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).mul
    ((particle_contDiffAt_positive hf hu (p.1+p.2.1) p.2.2).continuousAt.comp (f:=fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) hm)

lemma source_receiver_packet_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t Q : ℝ),t≤U → 0≤Q →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*Q/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t Q htU hQ hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by ring))

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_MagneticVolterra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma source_receiver_packet_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t : ℝ) (g : ℝ → ℝ),t≤U → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*g (t-‖z‖)/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t g htU hg0 hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hQ : 0≤g (t-coneRadius 0 z) := hg0 _ ⟨hu.1.le,hu.2⟩
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*g (t-coneRadius 0 z)*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by simp only [coneRadius,zero_sub,norm_neg]; ring))

lemma magnetic_source_receiver_integral_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) t,∫ v,sourceReceiverParticlePacket s t e i (x,z,v)|≤
        C*H*(∫ u in Icc (0:ℝ) t,g u) := by
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_volterra_bound P A M e i hA
  let V := volume.real (closedBall (0:Vec) P)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨4*Real.pi*V*K,by positivity,?_⟩
  intro s U t H x g ht htU hUH hg hg0 hE hB hfA hP hEB hDF
  have hH : 0≤H := ht.trans (htU.trans hUH)
  rw [←Real.norm_eq_abs]
  apply (kernel_volterra_norm_subset ht (C:=V*K*H) (by positivity) measurableSet_ball
    (Subset.rfl) hg (fun u hu => hg0 u ⟨hu.1,hu.2.trans htU⟩) ?_).trans_eq (by ring)
  intro z hz hz0
  have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  have hgu : 0≤g (t-‖z‖) := by simpa only [coneRadius,zero_sub,norm_neg] using hg0 _ hu
  have hh := norm_velocity_integral_bound (P:=P) (g:=fun v => sourceReceiverParticlePacket s t e i (x,z,v))
    (fun v hv => by simp only [sourceReceiverParticlePacket,hP _ hu _ v hv,mul_zero])
    (hkb s U t g htU hg0 hE hB hfA hEB hDF x z · hz0 hzt)
  apply hh.trans
  change V*(K*g (t-‖z‖)/‖z‖)≤_
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz0
  calc
    _ = (V*K*g (t-‖z‖)*‖z‖)/‖z‖^2 := by field_simp
    _ ≤ (V*K*g (t-‖z‖)*H)/‖z‖^2 := by gcongr; exact hzt.le.trans (htU.trans hUH)
    _ = _ := by ring

lemma magnetic_source_deriv_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H N : ℝ) (x : Vec) (g : ℝ → ℝ),
      0<t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
        sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := magnetic_source_particle_gradient_volterra_bound P A M e i hA
  obtain ⟨C₂,hC₂,hb₂⟩ := magnetic_source_receiver_integral_volterra_bound P A M e i hA
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN
  obtain ⟨Q₀,hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f:=g) hg.continuousOn
  let Q := max Q₀ 0
  have hQ : 0≤Q := le_max_right _ _
  have hDFconst : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q := by
    intro u hu y
    have hh : g u≤Q := (le_abs_self _).trans ((hQ₀ u ⟨hu.1.le,hu.2⟩).trans (le_max_left _ _))
    exact ⟨(hDF u hu y).1.trans hh,(hDF u hu y).2.trans hh⟩
  have hH : 0≤H := ht.le.trans (htU.trans hUH)
  have hprop (z : Vec) (hz : ‖z‖<t) : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  let R := sourceReceiverParticlePacket s t e i
  let F := fun p : Vec × Phase => fderiv ℝ (sourceWeightedPacket s t i) p (e,0,0)
  have hRc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt R p :=
    fun p hp hpt => sourceReceiverParticlePacket_continuousAt e i hf hE hB hp hpt
  have hRz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → R (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [R,sourceReceiverParticlePacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hweighted : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p :=
    fun p hp hpt => sourceWeightedPacket_contDiffAt i hf hE hB hp (hprop p.2.1 hpt).1
  have hWz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → sourceWeightedPacket s t i (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hFc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p := by
    intro p hp hpt
    exact ((hweighted p hp hpt).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hFz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0 :=
    fun x z v hz hzt hv => retarded_packet_derivative_zero hweighted hWz x z v e hz hzt hv
  have hRi := retarded_packet_integrable x hRc hRz (hkb s U t Q htU hQ hE hB hfA hEB hDFconst)
  have hPi := source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN
  have hsplit : (∫ z in ball (0:Vec) t,∫ v,F (x,z,v))=
      (∫ z in ball (0:Vec) t,∫ v,R (x,z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) := by
    rw [←integral_add hRi hPi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    have hFi := retarded_packet_inner_integrable hFc hFz x z hz0 hzt
    have hRi' := retarded_packet_inner_integrable hRc hRz x z hz0 hzt
    have hh : (∫ v,F (x,z,v))-(∫ v,R (x,z,v))=
        ∫ v,sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
      rw [←integral_sub hFi hRi']
      apply integral_congr_ae
      exact ae_of_all _ (fun v => by
        dsimp [F,R,sourceReceiverParticlePacket]
        rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz0 (hprop z hzt).1]
        ring)
    linarith
  rw [(hasDerivAt_magnetic_source_integral x e i 0 htU hf hE hB hA hN hQ hP hfA hEB hDFconst hfN).deriv]
  simp only [zero_smul,add_zero]
  change |∫ z in ball (0:Vec) t,∫ v,F (x,z,v)|≤_
  rw [hsplit]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hb₂ s U t H x g ht.le htU hUH hg hg0 hE hB hfA hP hEB hDF)
    (hb₁ s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN)).trans
  have hJ : 0≤∫ u in Icc (0:ℝ) t,1+g u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity)
  have hG : 0≤∫ u in Icc (0:ℝ) t,g u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => hg0 u ⟨hu.1,hu.2.trans htU⟩)
  have hGJ : (∫ u in Icc (0:ℝ) t,g u)≤∫ u in Icc (0:ℝ) t,1+g u :=
    integral_mono hg.integrableOn_Icc (continuous_const.add hg).integrableOn_Icc (fun u => by linarith)
  have hh : C₂*H*(∫ u in Icc (0:ℝ) t,g u)≤C₂*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
    have hmul : H*(∫ u in Icc (0:ℝ) t,g u)≤(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := by
      gcongr; linarith
    have hh' := mul_le_mul_of_nonneg_left (hmul.trans (le_add_of_nonneg_left hH)) hC₂
    nlinarith
  nlinarith

end RVM.Magnetic
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


namespace Magnetic

lemma source_density_integrable {s : Solution} {U t P A M : ℝ} (x : Vec) (i : Fin 3)
    (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (_hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v))
      (ball (0:Vec) t) := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  have hu {z : Vec} (hzt : ‖z‖<t) : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  apply retarded_packet_integrable (F:=sourceWeightedPacket s t i) (P:=P) (C:=K*A) x
  · intro p hp hpt
    exact (sourceWeightedPacket_contDiffAt i hf hE hB hp (by
      simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hpt)).continuousAt
  · intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ (hu hzt) _ v hv,mul_zero]
  · intro x z v hz hzt hv
    change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul (hkb s t x z v hz hv (hEB _ (hu hzt) _).1 (hEB _ (hu hzt) _).2)
      (hfA _ (hu hzt) _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)

lemma retardedMagneticDensity_split {s : Solution} {t : ℝ} (x z : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hz : z≠0) (ht : 0≤t-coneRadius 0 z) :
    retardedMagneticDensity s t x (x+z) i =
      (∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
      (∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) := by
  have hxy : x≠x+z := by intro he; exact hz (add_left_cancel (show x+z=x+0 by simpa using he.symm))
  have hr : coneRadius x (x+z)=coneRadius 0 z := by simp [coneRadius]
  have hn : coneDirection x (x+z)=coneDirection 0 z := by simp [coneDirection,coneRadius]
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht (x+z)
  have htc : Continuous (fun v => transportConeCoefficient i (z,v)) := (transport_kernel_velocity_contDiff i hz).continuous
  have hsc : Continuous (fun v => sourceConeCoefficient s t x i (z,v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (contDiffAt_const.mul ((sourceAngularProfile_contDiffAt i
      (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').comp v
        (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
  have hti := (htc.mul hreg.continuous).integrable_of_hasCompactSupport (μ:=volume) hcomp.mul_left
  have hsi := (hsc.mul hreg.continuous).integrable_of_hasCompactSupport (μ:=volume) hcomp.mul_left
  change Integrable (fun v => transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) at hti
  change Integrable (fun v => sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) at hsi
  rw [retardedMagneticDensity_component hf hc hxy (by simpa only [hr] using ht) i,←integral_add hti hsi]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    have hh := congrArg (fun a : Vec => a i) (physicalMagneticKernel_eulerian_split
      (fderiv ℝ velocity v (s.E (t-coneRadius 0 z,x+z)+cross (velocity v) (s.B (t-coneRadius 0 z,x+z))))
      (show coneRadius 0 z≠0 by simpa [coneRadius] using hz) (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne')
    simp only [PiLp.smul_apply,smul_eq_mul,PiLp.add_apply] at hh
    simp only [hr,hn,
      transportConeCoefficient,sourceConeCoefficient,sourceFixedCoefficient,sourceAngularProfile]
    linear_combination s.f (t-coneRadius 0 z,x+z,v)*hh)

end Magnetic


namespace Magnetic

lemma classical_magnetic_transport_source_before {d : Datum} {s : Solution} {U t P A M : ℝ}
    (hs : ClassicalBefore d s U) (hm : SmoothOnFiniteHorizons s) (x : Vec) (i : Fin 3)
    (ht : 0<t) (htU : t<U) (hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) :
    s.B (t,x) i=magneticBoundaryField (datumBoundarySolution d) t x i+(4*Real.pi)⁻¹*
      ((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v))) := by
  have hti := transport_density_integrable x i htU.le hs.1 hA hP hfA
  have hsi := source_density_integrable x i htU.le hs.1 hs.2.1 hs.2.2.1 hA hP hfA hEB
  have hdens := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hdens
  simp only [PiLp.proj_apply] at hp
  have hsplit : (∫ z in ball (0:Vec) t,retardedMagneticDensity s t x (x+z) i)=
      (∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) := by
    rw [←integral_add hti hsi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact retardedMagneticDensity_split x z i hs.1 hs.2.2.2.2.2.2.1 hz0 (by
      simpa only [coneRadius,zero_sub,norm_neg] using (sub_nonneg.mpr (show ‖z‖≤t from
        (show ‖z‖<t by simpa only [mem_ball,dist_zero_right] using hz).le)))
  have hh := congrArg (fun a : Vec => a i) (classical_magnetic_physical_vector_before hs hm ht htU x)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hh
  have hbd : magneticBoundaryField s t x i=magneticBoundaryField (datumBoundarySolution d) t x i :=
    classical_magneticConeBoundary_datum_before hs ht x i
  rw [hbd,←hp,hsplit] at hh
  exact hh

end Magnetic


lemma hasDerivAt_vec_component_line {g : Vec → Vec} {x e : Vec} (i : Fin 3)
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun q : ℝ => g (x+q • e) i) ((fderiv ℝ g x e) i) 0 := by
  have hl : HasDerivAt (fun q : ℝ => x+q • e) e 0 := by
    convert ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x using 1 <;> first | rfl | simp
  have hg' : HasFDerivAt g (fderiv ℝ g x) (x+(0:ℝ) • e) := by simpa only [zero_smul,add_zero] using hg.hasFDerivAt
  have hh := hg'.comp_hasDerivAt (0:ℝ) hl
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt (0:ℝ) hh
  simpa only [Function.comp_def,PiLp.proj_apply] using hp

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


namespace Magnetic

lemma classical_magnetic_gradient_volterra_bound_oai {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → 0≤N → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨B,C,D,hB,hC,hD,hT⟩ := magnetic_transport_deriv_bound P A M H e i hA hH
  obtain ⟨K,hK,hS⟩ := magnetic_source_deriv_volterra_bound P A M e i hA
  obtain ⟨J,hJ,hJi,hJb⟩ := datum_boundary_global_jets_horizon hd H hH 1
  let c := (4*Real.pi)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨J*‖e‖+c*(B+D*Real.log (max 1 H)+K*H),C,c*D,c*K*(1+H),
    ?_,hC,by positivity,by positivity,?_⟩
  · have hl : 0≤Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
    positivity
  intro s U t N x g hs hm ht htU hUH hN hg hg0 hfA hP hEB hDF hfN
  obtain ⟨Q₀,hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f:=g) hg.continuousOn
  let Q := max Q₀ 0
  have hQ : 0≤Q := le_max_right _ _
  have hDFconst : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q := by
    intro u hu y
    have hh : g u≤Q := (le_abs_self _).trans ((hQ₀ u ⟨hu.1.le,hu.2⟩).trans (le_max_left _ _))
    exact ⟨(hDF u hu y).1.trans hh,(hDF u hu y).2.trans hh⟩
  have hboundary := (hJb t ⟨ht,htU.le.trans hUH⟩).1.2
  let b := magneticBoundaryField (datumBoundarySolution d) t
  have hbd := hasDerivAt_vec_component_line (x:=x) (e:=e) i (hboundary.differentiable (by simp)).differentiableAt
  have hbd_bound : |fderiv ℝ b x e i|≤J*‖e‖ := by
    apply (norm_coordinate_le _ i).trans
    apply (ContinuousLinearMap.le_opNorm _ e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
    simpa only [norm_iteratedFDeriv_one] using (hJb t ⟨ht,htU.le.trans hUH⟩).2 x |>.2
  have htd := hasDerivAt_magnetic_transport_integral x e i 0 ht htU.le hs.1 hA hN hP hfA hfN
  have hsd := hasDerivAt_magnetic_source_integral x e i 0 htU.le hs.1 hs.2.1 hs.2.2.1 hA hN hQ hP hfA hEB hDFconst hfN
  have htotal := hbd.add ((htd.add hsd).const_mul c)
  have heq : (fun q : ℝ => s.B (t,x+q • e) i)=fun q : ℝ =>
      b (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))) := by
    funext q
    exact classical_magnetic_transport_source_before hs hm (x+q • e) i ht htU hA hP hfA hEB
  change HasDerivAt (fun q : ℝ =>
      b (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)))) _ 0 at htotal
  rw [heq,htotal.deriv]
  have htbound := hT s U t N x ht htU.le hUH hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hfN
  have hsbound := hS s U t H N x g ht htU.le hUH hg hg0 hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hDF hfN
  rw [htd.deriv] at htbound
  rw [hsd.deriv] at hsbound
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hc]
  apply (add_le_add hbd_bound (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add htbound hsbound)) hc)).trans_eq
  ring

end Magnetic

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound_oai := @OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound_oai
