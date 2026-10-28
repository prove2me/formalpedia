-- Prove2me | solution 1 for OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:06:54.102446+00:00
-- url     : https://prove2.me/submissions/3cff8c33-f955-4b6e-852b-e3d59567dc34

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_classical_shifted_electric_physical_representation_before
import Theorems.Thm_OAI_RVM_classical_shifted_magnetic_physical_representation_before

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

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma velocity_self (v : Vec) : dot (velocity v) (velocity v) = 1 - (q v)⁻¹ ^ 2 := by
  rw [velocity, dot_smul_left, dot_smul_right, dot_self]
  have hq := q_sq v
  have hn := ne_of_gt (q_pos v)
  field_simp
  nlinarith

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

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

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

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PositiveExtension
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

section PositiveExtension
variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_positiveTimeCut (a : ℝ) : ContDiff ℝ ∞ (positiveTimeCut a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (a/4))
lemma positiveTimeCut_zero {a t : ℝ} (ha : 0<a) (ht : t≤a/4) : positiveTimeCut a t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))
lemma positiveTimeCut_one {a t : ℝ} (ha : 0<a) (ht : a/2≤t) : positiveTimeCut a t=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0<a/4)).mpr
  linarith

end PositiveExtension

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

lemma integrableOn_retardedElectricDensity_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt
  have hcont := (contDiffOn_retardedElectricDensity hf hE hB hc ht x).continuousOn
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
  have hcont' := hcont.comp (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound_le hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (C:=C) (α:=2) (by norm_num) hcont'
  intro z hz hzR
  have hh := hbound z hz hzR.le
  change ‖retardedElectricDensity s t x (x+z)‖≤C*‖z‖^(-(2:ℝ))
  rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  exact hh

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

lemma continuousOn_electric_flux_boundary {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun p : ℝ × Vec => retardedElectricFlux s T x i (x+(T-p.1) • p.2))
      (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  have hw (z : Phase) (hz : x≠z.1) : ContinuousAt (fun z : Phase => retardedG x z i • velocity z.2) z :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp
      (contDiffAt_retardedG (k:=1) hz).continuousAt).smul
      ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousAt
  apply (continuousOn_weighted_cone_boundary hf hc hT x hw).congr
  intro p hp
  unfold retardedElectricFlux retardedDensity
  dsimp only
  rw [coneBoundary_radius hT hp.1 hp.2 x,sub_sub_cancel]
  congr 1
  funext v
  simp only [smul_smul]

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

lemma RegularParticle.rho_continuous_slab {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0≤T) : ContinuousOn (fun p : ℝ × Vec => rho (fun z => f (p.1,z)) p.2)
      (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have h := hf.moment_continuous_slab (w:=fun _ => (1:ℝ)) continuous_const hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v, f (p.1,p.2,v) • (1:ℝ)) _ at h
  simpa only [rho,smul_eq_mul,mul_one] using h

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQ
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

lemma receiverQ_force (a n h : Vec) : receiverQ a n h=h+cross a (cross n h) := by
  ext i
  fin_cases i <;> simp [receiverQ,cross,dot,Fin.sum_univ_succ] <;> ring

lemma receiverQ_add (a n h k : Vec) : receiverQ a n (h+k)=receiverQ a n h+receiverQ a n k := by
  simp only [receiverQ,dot_add_right,smul_add,add_smul]
  module

lemma receiverQ_smul (a n h : Vec) (c : ℝ) : receiverQ a n (c • h)=c • receiverQ a n h := by
  simp only [receiverQ,dot_smul_right,smul_add,smul_smul]
  module

end RVM

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

lemma electricConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedElectricFlux s t x i (x+t • n.1)=
      retardedElectricFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedElectricFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold electricConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [rho,current,hf]

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

lemma physical_force_kernel (r : ℝ) (n a v b : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity v)) • receiverQ a n (physicalElectricKernel r n (velocity v) b) =
      forceTransportKernel r n a v+forceSourceKernel r n a v b := by
  have hd := (cone_denom_pos v n hn).ne'
  have hq := (q_pos v).ne'
  have h1 : (1-dot n (velocity v))*((1-dot (velocity v) (velocity v))/(r^2*(1-dot n (velocity v))^3)) =
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ := by
    rw [velocity_self]
    field_simp
    ring
  have h2 : (1-dot n (velocity v))*(r*(1-dot n (velocity v))^3)⁻¹ =
      (r*(1-dot n (velocity v))^2)⁻¹ := by
    field_simp
  simp only [physicalElectricKernel,receiverQ_add,receiverQ_smul,smul_add,smul_smul,h1,h2,
    forceTransportKernel,forceSourceKernel,sourceNumerator]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQCLM
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma receiverQCLM_apply (a n h : Vec) : receiverQCLM a n h=receiverQ a n h := by
  simp only [receiverQCLM,add_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,crossCLM_apply,receiverQ_force]

lemma integral_receiverQ {H : Vec → Vec} (hH : Integrable H) (a n : Vec) :
    (∫ v : Vec, receiverQ a n (H v))=receiverQ a n (∫ v : Vec, H v) := by
  simpa only [receiverQCLM_apply] using (receiverQCLM a n).integral_comp_comm hH

lemma physical_lorentz_density {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} {x y : Vec} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (a : Vec) :
    retardedElectricDensity s t x y+cross a (retardedMagneticDensity s t x y)=
      ∫ v : Vec, retardedForceKernel s t x a y v := by
  change receiverQCLM a (coneDirection x y) (retardedElectricDensity s t x y)=_
  rw [receiverQCLM_apply,retardedElectricDensity,← integral_receiverQ
    (integrable_retardedElectricDensity_integrand hf hc hxy ht)]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [receiverQ_smul,mul_smul,physical_force_kernel _ _ _ _ _
    (show coneRadius x y≠0 by exact (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).ne')
    (coneDirection_norm hxy)]
  rfl

lemma ball_puncture_ae (R : ℝ) :
    (ball (0:Vec) R \ ({0} : Set Vec) : Set Vec) =ᵐ[volume] (ball (0:Vec) R : Set Vec) := by
  filter_upwards [volume.ae_ne (0:Vec)] with z hz
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩

lemma integrable_joint_of_punctured_norm_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : Vec × Vec → W} {R C α : ℝ} {K : Set Vec} (hα : α<3)
    (hK : IsCompact K)
    (hF : ContinuousOn F ((ball (0:Vec) R \ {0}) ×ˢ univ))
    (hz : ∀ z ∈ ball (0:Vec) R \ {0}, ∀ v ∉ K, F (z,v)=0)
    (hb : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → (∫ v : Vec, ‖F (z,v)‖)≤C*‖z‖^(-α)) :
    Integrable F ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  have hm : AEStronglyMeasurable F ((volume.restrict (ball (0:Vec) R)).prod volume) := by
    rw [← Measure.restrict_congr_set (ball_puncture_ae R)]
    have hh := hF.aestronglyMeasurable (μ:=volume.prod volume)
      ((measurableSet_ball.diff (measurableSet_singleton _)).prod MeasurableSet.univ)
    simpa only [← Measure.prod_restrict,Measure.restrict_univ] using hh
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzR hz0
    have hz' : z∈ball (0:Vec) R \ {0} := ⟨hzR,hz0⟩
    have hc : Continuous (fun v : Vec => F (z,v)) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz',mem_univ _⟩)
    exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz z hz'))
  · apply integrableOn_ball_of_punctured_bound hα
      (continuousOn_integral_uniform_support hK hF.norm (by
        intro z hz' v hv
        simp only [hz z hz' v hv,norm_zero]))
    intro z hz0 hzR
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb z hz0 hzR

lemma coneDirection_translate (x z : Vec) : coneDirection x (x+z)=coneDirection 0 z := by
  simp only [coneDirection,coneRadius,show x-(x+z) = -z by abel,zero_sub]

lemma continuousOn_coneDirection_zero {R : ℝ} :
    ContinuousOn (coneDirection (0:Vec)) (ball (0:Vec) R \ {0}) := by
  intro z hz
  have h0z : (0:Vec)≠z := by simpa only [mem_singleton_iff,ne_comm] using hz.2
  exact (contDiffAt_coneDirection (k:=1) h0z).continuousAt.continuousWithinAt

lemma integrable_radial_lift {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {R : ℝ} {K : Set Vec} {F : (Vec × Vec) × Vec → W}
    (hK : IsCompact K)
    (hF : ContinuousOn F ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ))
    (hz : ∀ z ∈ closedBall (0:Vec) R, ∀ n ∈ sphere (0:Vec) 1, ∀ v ∉ K, F ((z,n),v)=0) :
    Integrable (fun p : Vec × Vec => (‖p.1‖^2)⁻¹ • F ((p.1,coneDirection 0 p.1),p.2))
      ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  let S : Set Vec := ball (0:Vec) R \ {0}
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  have hN : ContinuousOn (fun z : Vec => (‖z‖^2)⁻¹) S :=
    (continuous_norm.pow 2).continuousOn.inv₀ (by
      intro z hz'
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz'.2))
  have harg : ContinuousOn (fun p : Vec × Vec => ((p.1,coneDirection 0 p.1),p.2)) (S ×ˢ univ) :=
    (continuous_fst.continuousOn.prodMk
      (continuousOn_coneDirection_zero.comp continuous_fst.continuousOn (fun _ h => h.1))).prodMk
      continuous_snd.continuousOn
  have hmap : MapsTo (fun p : Vec × Vec => ((p.1,coneDirection 0 p.1),p.2)) (S ×ˢ univ) (P ×ˢ univ) := by
    intro p hp
    refine ⟨⟨ball_subset_closedBall hp.1.1,?_⟩,mem_univ _⟩
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm (Ne.symm hp.1.2)
  have hcont : ContinuousOn (fun p : Vec × Vec => (‖p.1‖^2)⁻¹ • F ((p.1,coneDirection 0 p.1),p.2))
      (S ×ˢ univ) :=
    (hN.comp continuous_fst.continuousOn (fun _ h => h.1)).smul (hF.comp harg hmap)
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK hF.norm
    (by intro p hp v hv; simp only [hz p.1 hp.1 p.2 hp.2 v hv,norm_zero])
  apply integrable_joint_of_punctured_norm_bound (C:=C) (α:=2) (by norm_num) hK hcont
  · intro z hzs v hv
    have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
      simpa only [mem_sphere,dist_zero_right] using coneDirection_norm (Ne.symm hzs.2)
    rw [hz z (ball_subset_closedBall hzs.1) _ hn v hv,smul_zero]
  · intro z hz0 hzR
    have hz' : z∈closedBall (0:Vec) R := mem_closedBall_zero_iff.mpr hzR.le
    have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
      simpa only [mem_sphere,dist_zero_right] using coneDirection_norm (Ne.symm (norm_pos_iff.mp hz0))
    have hb := hbound (z,coneDirection 0 z) ⟨hz',hn⟩
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hb
    simp only [norm_smul,Real.norm_of_nonneg (show 0≤(‖z‖^2)⁻¹ by positivity),integral_const_mul]
    rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two,mul_comm C]
    exact mul_le_mul_of_nonneg_left hb (by positivity)

lemma integrable_retarded_weighted_radial {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    Integrable (fun p : Vec × Vec => (‖p.1‖^2)⁻¹ •
      (s.f (t-‖p.1‖,x+p.1,p.2) • A ((p.1,coneDirection 0 p.1),p.2)))
      ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  have ht : 0≤t := le_trans hR hRt
  obtain ⟨K,hK,hz⟩ := hc t ht
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  apply integrable_radial_lift (hK.image continuous_snd) (hcf.smul hA)
  intro z hz' n hn v hv
  have hsf : s.f (t-‖z‖,x+z,v)=0 := by
    by_contra hne
    exact hv ⟨(x+z,v),hz _ (htime z hz') (subset_tsupport _ hne),rfl⟩
  change s.f (t-‖z‖,x+z,v) • A ((z,n),v)=0
  rw [hsf,zero_smul]

lemma continuousOn_receiverQ {H : Type*} [TopologicalSpace H] {S : Set H}
    {a n h : H → Vec} (ha : ContinuousOn a S) (hn : ContinuousOn n S) (hh : ContinuousOn h S) :
    ContinuousOn (fun p => receiverQ (a p) (n p) (h p)) S := by
  exact ((continuousOn_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (hn.prodMk ha))).smul hh).add
      (((contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (ha.prodMk hh)).smul hn)

lemma continuousOn_retardedNormalisedForce {s : Solution}
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    {t R : ℝ} (hRt : R≤t) (x a : Vec) :
    ContinuousOn (retardedNormalisedForce s t x a)
      ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ) := by
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
  exact hD.continuousOn.smul (continuousOn_receiverQ continuousOn_const hn.continuousOn hN)

lemma radial_retardedNormalisedForce_eq (s : Solution) (t : ℝ) (x a z v : Vec) (hz : z≠0) :
    (‖z‖^2)⁻¹ • (s.f (t-‖z‖,x+z,v) • retardedNormalisedForce s t x a ((z,coneDirection 0 z),v)) =
      retardedForceKernel s t x a (x+z) v := by
  simp only [retardedNormalisedForce,retardedForceKernel,coneRadius_add,coneDirection_translate]
  rw [normalisedElectricKernel_eq (norm_ne_zero_iff.mpr hz),receiverQ_smul]
  rw [← physical_force_kernel _ _ _ _ _ (norm_ne_zero_iff.mpr hz)
    (coneDirection_norm (Ne.symm hz))]
  simp only [smul_smul]
  congr 1
  field_simp

lemma integrable_joint_retardedForceKernel {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x a : Vec) :
    Integrable (fun p : Vec × Vec => retardedForceKernel s t x a (x+p.1) p.2)
      ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  have hi := integrable_retarded_weighted_radial hf hc hR hRt x
    (continuousOn_retardedNormalisedForce hE hB hRt x a)
  apply hi.congr
  have hne : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), z≠0 :=
    ae_restrict_of_ae (volume.ae_ne (0:Vec))
  filter_upwards [MeasureTheory.Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hne] with p hp
  exact radial_retardedNormalisedForce_eq s t x a p.1 p.2 hp

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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

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

lemma continuousOn_electricConeBoundary_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (electricConeBoundary s T x i) (Icc 0 (T/2)) := by
  have hc := hs.2.2.2.2.2.2.1
  have hE : ContDiffOn ℝ ∞ s.E (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.1.mono (fun p hp => hp.1)
  have hB : ContDiffOn ℝ ∞ s.B (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.2.mono (fun p hp => hp.1)
  have hcurl := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
    (continuousOn_slab_curl hT (hB.of_le (by decide)))
  have hfree := (continuousOn_freeWave_slab hT hE hcurl x i).mono
    (show Icc 0 (T/2) ⊆ Icc 0 T from fun a ha => ⟨ha.1,by linarith [ha.2]⟩)
  have hflux := continuousOn_electric_flux_boundary hs.1 hc hT x i
  have hdot := (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hflux)
  have hflux' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).pow 2).mul hdot)
  have hrho := continuousOn_cone_boundary_comp hT (hs.regularParticle.rho_continuous_slab hT.le) x
  have hni : Continuous (fun p : ℝ × Vec => p.2 i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_snd
  have hrho' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).mul hni.continuousOn).mul hrho)
  have hj := continuousOn_cone_boundary_comp hT (hs.regularParticle.current_continuous_slab hT.le) x
  have hji := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn hj
  have hj' := continuousOn_integral_sphere hji
  exact ((hfree.sub (hflux'.const_mul ((4*Real.pi)⁻¹))).sub
    (hrho'.const_mul ((4*Real.pi)⁻¹))).sub
      ((((continuousOn_const (c:=T)).sub continuousOn_id).mul hj').const_mul ((4*Real.pi)⁻¹))

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

lemma classical_electric_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (hH : T < H) (x : Vec) (i : Fin 3) :
    s.E (T,x) i = electricConeBoundary s T x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedElectricDensity s T x (x+z) i) := by
  have hc := hs.2.2.2.2.2.2.1
  have hD : IntegrableOn (fun z => retardedElectricDensity s T x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1 hc hT.le le_rfl x)
  have hlim := (tendsto_right_of_continuousOn_Icc (show 0<T/2 by linarith)
    (continuousOn_electricConeBoundary_before hs hm hT x i)).add
    ((integral_ball_radius_tendsto hT hD).const_mul ((4*Real.pi)⁻¹))
  have heq : (fun a : ℝ => electricConeBoundary s T x i a + (4*Real.pi)⁻¹ *
      (∫ z in ball (0:Vec) (T-a), retardedElectricDensity s T x (x+z) i)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => s.E (T,x) i) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    have he := classical_shifted_electric_physical_representation_before hs hm ha.1
      (show 0<T-a by linarith [ha.2]) (by linarith) x i
    rw [show a+(T-a)=T by ring] at he
    unfold electricConeBoundary
    linarith
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds |>.symm

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

lemma classical_electric_physical_vector_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) := by
  have hD := integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  ext i
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
  exact (classical_electric_physical_representation_before hs hm ht hH x i).trans
    (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
      smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

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

lemma classical_physical_force_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce s t x a+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
        retardedElectricDensity s t x (x+z)+cross a (retardedMagneticDensity s t x (x+z)) := by
  have hE := integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hB := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hc := (crossCLM a).integral_comp_comm hB
  have hcross : IntegrableOn (fun z => cross a (retardedMagneticDensity s t x (x+z)))
      (ball (0:Vec) t) := by
    simpa only [IntegrableOn,crossCLM_apply] using (crossCLM a).integrable_comp hB
  have hc' : (∫ z in ball (0:Vec) t, cross a (retardedMagneticDensity s t x (x+z))) =
      cross a (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) := by
    simpa only [crossCLM_apply] using hc
  rw [classical_electric_physical_vector_before hs hm ht hH x,classical_magnetic_physical_vector_before hs hm ht hH x,
    integral_add hE hcross,hc']
  simp only [boundaryLorentzForce,cross_add_right,cross_smul_right]
  module

lemma classical_electricConeBoundary_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary (datumBoundarySolution d) t x i 0 :=
  electricConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

lemma classical_magneticConeBoundary_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary (datumBoundarySolution d) t x i 0 :=
  magneticConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

lemma classical_boundaryLorentzForce_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x a : Vec) :
    boundaryLorentzForce s t x a=boundaryLorentzForce (datumBoundarySolution d) t x a := by
  have hE : electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_electricConeBoundary_datum_before hs ht x i
  have hB : magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_magneticConeBoundary_datum_before hs ht x i
  simp only [boundaryLorentzForce,hE,hB]

lemma classical_retarded_force_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, ∫ v : Vec, retardedForceKernel s t x a (x+z) v := by
  rw [classical_physical_force_representation_before hs hm ht hH,classical_boundaryLorentzForce_datum_before hs ht]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  apply physical_lorentz_density hs.1 hs.2.2.2.2.2.2.1
  · intro he
    exact hz0 (add_left_cancel (show x+z=x+0 by simpa using he.symm))
  · rw [coneRadius_add]
    exact sub_nonneg.mpr (show ‖z‖≤t from (mem_ball_zero_iff.mp hz).le)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_UpperTimeCut
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

lemma contDiff_upperTimeCut (τ H : ℝ) : ContDiff ℝ ∞ (upperTimeCut τ H) :=
  (contDiff_positiveTimeCut _).comp (contDiff_const.sub contDiff_id)

lemma upperTimeCut_nonneg (τ H t : ℝ) : 0 ≤ upperTimeCut τ H t :=
  Real.smoothTransition.nonneg _

lemma upperTimeCut_one {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ) :
    upperTimeCut τ H t = 1 := by
  apply positiveTimeCut_one (by linarith)
  linarith

lemma upperTimeCut_zero {τ H t : ℝ} (hτ : τ < H) (ht : (τ+H)/2 ≤ t) :
    upperTimeCut τ H t = 0 := by
  apply positiveTimeCut_zero (by linarith)
  linarith

section Generic
variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma upperTimeExtend_eq {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ)
    (F : ℝ × X → W) (x : X) : upperTimeExtend τ H F (t,x)=F (t,x) := by
  simp only [upperTimeExtend,upperTimeCut_one hτ ht,one_smul]

omit [NormedSpace ℝ X] in
lemma upperTimeExtend_eventually_zero {τ H : ℝ} (hτ : τ < H)
    (F : ℝ × X → W) {p : ℝ × X} (hp : (τ+H)/2 < p.1) :
    upperTimeExtend τ H F =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
  simp only [upperTimeExtend,upperTimeCut_zero hτ hq.le,zero_smul]

lemma contDiffOn_upperTimeExtend {τ H : ℝ} (hτ : τ < H) {F : ℝ × X → W}
    (hF : ContDiffOn ℝ ∞ F {p | p.1 ∈ Icc 0 H}) :
    ContDiffOn ℝ ∞ (upperTimeExtend τ H F) {p | 0 ≤ p.1} := by
  intro p hp
  by_cases hpt : p.1 < H
  · have hlocal : {q : ℝ × X | q.1 ∈ Icc 0 H} ∈ 𝓝[{q | 0 ≤ q.1}] p := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_fst continuous_const).mem_nhds hpt),
        self_mem_nhdsWithin] with q hq hq0
      exact ⟨hq0,hq.le⟩
    exact (((contDiff_upperTimeCut τ H).comp contDiff_fst).contDiffAt.contDiffWithinAt).smul
      ((hF p ⟨hp,hpt.le⟩).mono_of_mem_nhdsWithin hlocal)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (upperTimeExtend_eventually_zero hτ F (show (τ+H)/2 < p.1 by linarith))).contDiffWithinAt

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma derivWithin_upperTimeExtend {τ H t : ℝ} (hτ : τ < H) (ht : t < τ)
    (F : ℝ × X → W) (x : X) (S : Set ℝ) :
    derivWithin (fun r => upperTimeExtend τ H F (r,x)) S t =
      derivWithin (fun r => F (r,x)) S t := by
  have he : (fun r => upperTimeExtend τ H F (r,x)) =ᶠ[𝓝 t] (fun r => F (r,x)) := by
    filter_upwards [Iio_mem_nhds ht] with r hr
    exact upperTimeExtend_eq hτ hr.le F x
  exact he.filter_mono nhdsWithin_le_nhds |>.derivWithin_eq (upperTimeExtend_eq hτ ht.le F x)
end Generic

lemma timeContinuousL2_upperTimeExtend {τ H : ℝ} (hτ : τ < H) (hH : 0 ≤ H)
    {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn F₂ (Icc 0 H) ∧ ∀ t ∈ Icc 0 H,
        (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 (upperTimeExtend τ H F) := by
  obtain ⟨F₂,hc,he⟩ := hF
  refine ⟨fun t => upperTimeCut τ H t • F₂ (min t H),?_,?_⟩
  · exact (contDiff_upperTimeCut τ H).continuous.continuousOn.smul
      (hc.comp (continuous_id.min continuous_const).continuousOn
        (fun t ht => ⟨le_min ht hH,min_le_right _ _⟩))
  · intro t ht
    have hl := Lp.coeFn_smul (upperTimeCut τ H t) (F₂ (min t H))
    by_cases htH : t ≤ H
    · rw [min_eq_left htH] at hl
      filter_upwards [hl,he t ⟨ht,htH⟩] with x hx hx'
      simpa only [min_eq_left htH,upperTimeExtend,Pi.smul_apply,hx'] using hx
    · have hz := upperTimeCut_zero hτ (show (τ+H)/2 ≤ t by linarith)
      filter_upwards [hl] with x hx
      simpa only [hz,upperTimeExtend,zero_smul,Pi.zero_apply,Pi.smul_apply] using hx

lemma cutoffPrefix_eq {τ H t : ℝ} (hτH : τ < H) (ht : t ≤ τ) (s : Solution) :
    (∀ z, (cutoffPrefix τ H s).f (t,z)=s.f (t,z)) ∧
    (∀ x, (cutoffPrefix τ H s).E (t,x)=s.E (t,x)) ∧
    (∀ x, (cutoffPrefix τ H s).B (t,x)=s.B (t,x)) :=
  ⟨upperTimeExtend_eq hτH ht s.f,upperTimeExtend_eq hτH ht s.E,
    upperTimeExtend_eq hτH ht s.B⟩

lemma cutoffPrefix_equations {s : Solution} {τ H : ℝ} (hτH : τ < H)
    (hs : EquationsBefore s H) : EquationsBefore (cutoffPrefix τ H s) τ := by
  intro t ht htτ
  have hh := hs t ht (htτ.trans hτH)
  have hf (x v : Vec) := derivWithin_upperTimeExtend hτH htτ s.f (x,v) (Ici 0)
  have hE (x : Vec) := derivWithin_upperTimeExtend hτH htτ s.E x (Ici 0)
  have hB (x : Vec) := derivWithin_upperTimeExtend hτH htτ s.B x (Ici 0)
  change (∀ x v, derivWithin (fun r => upperTimeExtend τ H s.f (r,x,v)) (Ici 0) t + _ + _ = 0) ∧ _
  simp only [cutoffPrefix]
  simp only [hf,hE,hB]
  simpa only [upperTimeExtend,upperTimeCut_one hτH htτ.le,one_smul] using hh

lemma SmoothClassicalPrefix.cutoff_smooth {d : Datum} {s : Solution} {τ H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hτH : τ < H) :
    SmoothOnFiniteHorizons (cutoffPrefix τ H s) := by
  intro T _hT
  exact ⟨(contDiffOn_upperTimeExtend hτH hs.f_smooth).mono (fun _ hp => hp.1),
    (contDiffOn_upperTimeExtend hτH hs.E_smooth).mono (fun _ hp => hp.1),
    (contDiffOn_upperTimeExtend hτH hs.B_smooth).mono (fun _ hp => hp.1)⟩

lemma SmoothClassicalPrefix.cutoff_classical_before {d : Datum} {s : Solution} {τ H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hτ : 0 ≤ τ) (hτH : τ < H) :
    ClassicalBefore d (cutoffPrefix τ H s) τ := by
  have hH : 0 ≤ H := hτ.trans hτH.le
  refine ⟨(contDiffOn_upperTimeExtend hτH hs.f_smooth).of_le (by decide),
    (contDiffOn_upperTimeExtend hτH hs.E_smooth).of_le (by decide),
    (contDiffOn_upperTimeExtend hτH hs.B_smooth).of_le (by decide),?_,
    timeContinuousL2_upperTimeExtend hτH hH hs.E_L2,
    timeContinuousL2_upperTimeExtend hτH hH hs.B_L2,?_,
    cutoffPrefix_equations hτH hs.equations,?_,?_,?_⟩
  · intro t ht z
    by_cases htH : t ≤ H
    · exact mul_nonneg (upperTimeCut_nonneg τ H t) (hs.nonnegative t ⟨ht,htH⟩ z)
    · simp only [cutoffPrefix,upperTimeExtend,
        upperTimeCut_zero hτH (show (τ+H)/2 ≤ t by linarith),zero_smul,le_refl]
  · obtain ⟨K,hK,hk⟩ := hs.compact
    intro T _hT
    refine ⟨K,hK,?_⟩
    intro t ht
    by_cases htH : t ≤ H
    · exact (tsupport_smul_subset_right (fun _ : Phase => upperTimeCut τ H t)
        (fun z => s.f (t,z))).trans (hk t ⟨ht.1,htH⟩)
    · simp only [cutoffPrefix,upperTimeExtend,
        upperTimeCut_zero hτH (show (τ+H)/2 ≤ t by linarith),zero_smul]
      change tsupport (0 : Phase → ℝ) ⊆ K
      simp only [tsupport_zero,empty_subset]
  · intro z
    exact (cutoffPrefix_eq hτH hτ s).1 z |>.trans (hs.initial_f z)
  · intro x
    exact (cutoffPrefix_eq hτH hτ s).2.1 x |>.trans (hs.initial_E x)
  · intro x
    exact (cutoffPrefix_eq hτH hτ s).2.2 x |>.trans (hs.initial_B x)

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

lemma normalisedSignedForce_flux {r : ℝ} (n a v b : Vec)
    (hr : r≠0) (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    (1-dot n a) • normalisedSignedForce r a (velocity v) n b=
      r^2 • (forceTransportKernel r n a v+forceSourceKernel r n a v b) := by
  rw [normalisedSignedForce,smul_smul]
  have hc : (1-dot n a)*((1-dot n (velocity v))/(1-dot n a))=1-dot n (velocity v) := by
    field_simp
  rw [hc,normalisedElectricKernel_eq hr,receiverQ_smul,smul_comm,
    ←physical_force_kernel r n a v b hr hn]

lemma coneRadius_sub_smul (x : Vec) (n : Sphere) {r : ℝ} (hr : 0 < r) :
    coneRadius x (x-r • n.1)=r := by
  simp only [coneRadius,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]

lemma coneDirection_sub_smul (x : Vec) (n : Sphere) {r : ℝ} (hr : 0 < r) :
    coneDirection x (x-r • n.1)=n.1 := by
  rw [coneDirection,coneRadius_sub_smul x n hr,sub_sub_cancel,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]

lemma retardedForceKernel_polar_normalised (s : Solution) (t : ℝ) (x a v : Vec)
    (n : Sphere) {r : ℝ} (hr : 0 < r) (hD : 1-dot n.1 a≠0) :
    r^2 • retardedForceKernel s t x a (x-r • n.1) v=
      (1-dot n.1 a) • (s.f (t-r,(x-r • n.1,v)) •
        normalisedSignedForce r a (velocity v) n.1
          (sourceAcceleration s (t-r,(x-r • n.1,v)))) := by
  rw [smul_comm (1-dot n.1 a),normalisedSignedForce_flux n.1 a v _ hr.ne' (sphere_norm n) hD]
  rw [smul_comm]
  congr 1
  simp only [retardedForceKernel,coneRadius_sub_smul x n hr,coneDirection_sub_smul x n hr,
    sourceAcceleration]

lemma classical_retarded_force_polar_before {d : Datum} {s : Solution} {H t : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s)
    (ht : 0<t) (htH : t<H) (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫r in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (t-r,(x-r • n.1,v)) •
          normalisedSignedForce r a (velocity v) n.1
            (sourceAcceleration s (t-r,(x-r • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  rw [classical_retarded_force_representation_before hs hm ht htH x a]
  congr 2
  have hi := integrable_joint_retardedForceKernel hs.1 hs.2.1.continuousOn
    hs.2.2.1.continuousOn hs.2.2.2.2.2.2.1 ht.le le_rfl x a
  rw [integral_ball_polar_flip hi.integral_prod_left]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [←integral_smul,←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>by
      rw [←sub_eq_add_neg]
      exact retardedForceKernel_polar_normalised s t x a v n hr.1
        (by
          have hh := dot_le_norm n.1 a
          rw [sphere_norm,one_mul] at hh
          linarith)))

lemma sourceAcceleration_cutoff {s : Solution} {τ H σ : ℝ} (hτH : τ<H)
    (hσ : σ≤τ) (p : Phase) :
    sourceAcceleration (cutoffPrefix τ H s) (σ,p)=sourceAcceleration s (σ,p) := by
  simp only [sourceAcceleration,(cutoffPrefix_eq hτH hσ s).2.1 p.1,
    (cutoffPrefix_eq hτH hσ s).2.2 p.1]

lemma SmoothClassicalPrefix.retarded_force_polar {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (htH : t<H)
    (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫r in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (t-r,(x-r • n.1,v)) •
          normalisedSignedForce r a (velocity v) n.1
            (sourceAcceleration s (t-r,(x-r • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  let τ := (t+H)/2
  have htτ : t<τ := by dsimp [τ]; linarith
  have hτH : τ<H := by dsimp [τ]; linarith
  have he := classical_retarded_force_polar_before
    (hs.cutoff_classical_before (ht.le.trans htτ.le) hτH) (hs.cutoff_smooth hτH)
    ht htτ x a ha
  rw [(cutoffPrefix_eq hτH htτ.le s).2.1 x,(cutoffPrefix_eq hτH htτ.le s).2.2 x] at he
  refine he.trans ?_
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have hσ : t-r≤τ := by linarith [hr.1]
    dsimp only
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>by
      dsimp only
      rw [(cutoffPrefix_eq hτH hσ s).1,sourceAcceleration_cutoff hτH hσ]))

lemma integral_Ioo_reflect {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : ℝ→W) {t : ℝ} (ht : 0≤t) :
    (∫σ in Ioo (0:ℝ) t,g (t-σ))=∫r in Ioo (0:ℝ) t,g r := by
  have he := intervalIntegral.integral_comp_sub_left (a:=0) (b:=t) g t
  simpa only [sub_self,sub_zero,intervalIntegral.integral_of_le ht,
    integral_Ioc_eq_integral_Ioo] using he

lemma SmoothClassicalPrefix.retarded_force_source_polar_oai {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (htH : t<H)
    (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫σ in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (σ,(x-(t-σ) • n.1,v)) •
          normalisedSignedForce (t-σ) a (velocity v) n.1
            (sourceAcceleration s (σ,(x-(t-σ) • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  rw [hs.retarded_force_polar ht htH x a ha]
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    rw [←integral_Ioo_reflect (fun r=> (1-dot n.1 a) • ∫v : Vec,
      s.f (t-r,(x-r • n.1,v)) • normalisedSignedForce r a (velocity v) n.1
        (sourceAcceleration s (t-r,(x-r • n.1,v)))) ht.le]
    simp only [sub_sub_cancel])

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar_oai := @OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar_oai
