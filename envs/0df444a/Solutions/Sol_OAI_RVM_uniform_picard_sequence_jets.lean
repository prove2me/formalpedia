-- Prove2me | solution 1 for OAI.RVM.uniform_picard_sequence_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:47:10.280284+00:00
-- url     : https://prove2.me/submissions/5b3f6fcd-5ec5-4064-a15a-13863603b5bb

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_datum_boundary_global_jets
import Theorems.Thm_OAI_RVM_mixed_electric_physical_representation
import Theorems.Thm_OAI_RVM_mixed_magnetic_physical_representation
import Theorems.Thm_OAI_RVM_physical_cone_derivative_tame
import Theorems.Thm_OAI_RVM_transported_derivative_tame

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

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

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

lemma coneBoundary_radius {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : coneRadius x (x+(T-a) • n)=T-a := by
  rw [coneRadius_add,norm_smul,Real.norm_of_nonneg (by linarith [ha.2]),
    show ‖n‖=1 by simpa only [mem_sphere,dist_zero_right] using hn,mul_one]

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

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBounds
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

lemma mixed_physical_vector {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t : ℝ} (ht : 0<t) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity {s with E:=E,B:=B} t x (x+z) ∧
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity {s with E:=E,B:=B} t x (x+z) := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  constructor
  · ext i
    have hD := integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_electric_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hρ hj hM ht x i).trans
      (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)
  · ext i
    have hD := integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_magnetic_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hj hM ht x i).trans
      (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PicardRegular.boundary_eq {d : Datum} {s : Solution} (hs : PicardRegular d s)
    {t : ℝ} (ht : 0<t) (x : Vec) :
    electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x ∧
    magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
  constructor
  · ext i
    exact electricConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i
  · ext i
    exact magneticConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PicardKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma normalisedPhysicalIntegrand_eq {r : ℝ} (hr : r≠0) (n v : Vec) (a : ℝ) (E B : Vec) :
    normalisedPhysicalIntegrand ((r,n,v),(a,E,B)) = r^2 •
      ((a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  simp only [normalisedPhysicalIntegrand,normalisedElectricKernel_eq hr]
  exact smul_comm _ _ _

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SmoothIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

section SpatialDerivatives
variable {A E W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_iteratedFDeriv_slice {F : A × E → W} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E W).symm.contDiff.comp hF
  | succ n ih =>
    let G : A × E → (E [×n]→L[ℝ] W) := fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    change ContDiff ℝ ∞ G at ih
    have he (p : A × E) : fderiv ℝ (fun x => G (p.1,x)) p.2 =
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ A E) := by
      have hin : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ A E) p.2 := by
        convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
      exact ((ih.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
    simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    change ContDiff ℝ ∞ (fun p : A × E =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm (fderiv ℝ (fun x => G (p.1,x)) p.2))
    simp_rw [he]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm.contDiff.comp
      ((ih.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const)

end SpatialDerivatives

section CompactFamily
variable {α : Type v} {E : Type u} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma SmoothCompactFamily.ofJoint {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {G : A × E → W} (hG : ContDiff ℝ ∞ G) {ι : α → A} (hι : Continuous ι) :
    SmoothCompactFamily (fun a x => G (ι a,x)) := by
  refine ⟨fun a => hG.comp (contDiff_const.prodMk contDiff_id),fun n => ?_⟩
  exact (contDiff_iteratedFDeriv_slice hG n).continuous.comp
    ((hι.comp continuous_snd).prodMk continuous_fst)

lemma SmoothCompactFamily.continuous {F : α → E → W} (hF : SmoothCompactFamily F) :
    Continuous (fun p : E × α => F p.2 p.1) := by
  have h := (continuousMultilinearCurryFin0 ℝ E W).continuous.comp (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply] using h

lemma SmoothCompactFamily.derivFamily {F : α → E → W} (hF : SmoothCompactFamily F) :
    SmoothCompactFamily (fun a => fderiv ℝ (F a)) := by
  refine ⟨fun a => (hF.1 a).fderiv_right (m:=∞) (by simp),fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fderiv ℝ (F p.2)) p.1 =
      continuousMultilinearCurryRightEquiv' ℝ n E W (iteratedFDeriv ℝ (n+1) (F p.2) p.1) := by
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  simp_rw [he]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E W).continuous.comp (hF.2 (n+1))

variable [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α]
  [ProperSpace E] [CompleteSpace W]

omit [CompleteSpace W] in
lemma hasFDerivAt_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) (x : E) :
    HasFDerivAt (fun y => ∫ a, F a y ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
  have hD := hF.derivFamily.continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall x 1) (bound:=fun _ => C) (F':=fun y a => fderiv ℝ (F a) y)
    (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun a y hy => hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun a y _ => ((hF.1 a).differentiable (by simp) y).hasFDerivAt)

lemma contDiff_integral_smoothFamily_nat (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ContDiff ℝ n (fun x => ∫ a, F a x ∂μ) := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiff_zero.mpr
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hF.continuous.continuousOn
    intro x a _ ha
    exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    rw [show (↑(n+1) : ℕ∞ω) = ↑n+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_smoothFamily μ hF x).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫ a, F a x ∂μ) = (fun x => ∫ a, fderiv ℝ (F a) x ∂μ) := by
      funext x
      exact (hasFDerivAt_integral_smoothFamily μ hF x).fderiv
    rw [he]
    exact ih hF.derivFamily

lemma contDiff_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) : ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  rw [contDiff_infty]
  exact fun n => contDiff_integral_smoothFamily_nat μ n hF

end CompactFamily

variable {E W : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

attribute [local instance] Measure.Subtype.measureSpace in
lemma contDiff_spatial_intervalIntegral {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a≤b) : ContDiff ℝ ∞ (fun y => ∫ r in a..b, F (r,y)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := contDiff_integral_smoothFamily (volume : Measure (Icc a b))
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val)
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  simpa only [he] using hh

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

lemma coneRadius_sub_smul (x : Vec) (n : Sphere) {r : ℝ} (hr : 0 < r) :
    coneRadius x (x-r • n.1)=r := by
  simp only [coneRadius,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]

lemma coneDirection_sub_smul (x : Vec) (n : Sphere) {r : ℝ} (hr : 0 < r) :
    coneDirection x (x-r • n.1)=n.1 := by
  rw [coneDirection,coneRadius_sub_smul x n hr,sub_sub_cancel,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]

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

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section

lemma smoothReciprocal_smooth {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (smoothReciprocal δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq (f:=fun _ : ℝ => (0:ℝ))
    have hne : ∀ᶠ y : ℝ in 𝓝 0, y<δ/2 := Iio_mem_nhds (by positivity)
    filter_upwards [hne] with y hy
    dsimp only [smoothReciprocal]
    rw [Real.smoothTransition.zero_of_nonpos,zero_div]
    apply sub_nonpos.mpr
    exact (div_le_iff₀ hδ).2 (by linarith)
  · exact (Real.smoothTransition.contDiff.contDiffAt.comp x
      ((contDiffAt_const.mul contDiffAt_id).div_const δ |>.sub contDiffAt_const)).div contDiffAt_id hx

lemma smoothReciprocal_eq {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    smoothReciprocal δ x=x⁻¹ := by
  unfold smoothReciprocal
  rw [Real.smoothTransition.one_of_one_le,one_div]
  apply le_sub_iff_add_le.mpr
  exact (le_div_iff₀ hδ).2 (by linarith)

lemma uniform_cone_denominator (P : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ n v : Vec,
    ‖n‖=1 → ‖v‖ ≤ P → δ ≤ 1-dot n (velocity v) := by
  let K : Set (Vec × Vec) := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  let D : Vec × Vec → ℝ := fun p => 1-dot p.1 (velocity p.2)
  have hD : Continuous D := continuous_const.sub
    ((contDiff_dot_pair (k:=∞)).continuous.comp (continuous_fst.prodMk ((contDiff_velocity (k:=∞)).continuous.comp continuous_snd)))
  have hp (p : Vec × Vec) (hp : p∈K) : 0<D p :=
    cone_denom_pos p.2 p.1 (by simpa only [mem_sphere,dist_zero_right] using hp.1)
  have hi : ContinuousOn (fun p => (D p)⁻¹) K := hD.continuousOn.inv₀ (fun p hp' => (hp p hp').ne')
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hi).isBounded.exists_norm_le
  refine ⟨(1+max C 0)⁻¹,by positivity,?_⟩
  intro n v hn hv
  have hm : (n,v)∈K := ⟨by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall_zero_iff] using hv⟩
  have hpos := hp (n,v) hm
  have hb := hC _ ⟨(n,v),hm,rfl⟩
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)] at hb
  exact (inv_le_comm₀ (by positivity) hpos).2 (hb.trans (by linarith [le_max_left C 0]))

lemma smoothNormalisedPhysical_smooth {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothNormalisedPhysical δ) := by
  let v : ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) → Vec := fun p => p.1.2.2
  have hv : ContDiff ℝ ∞ v := contDiff_fst.snd.snd
  have hu : ContDiff ℝ ∞ (fun p => velocity (v p)) := contDiff_velocity.comp hv
  have hn : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec) => p.1.2.1) := contDiff_fst.snd.fst
  have hb : ContDiff ℝ ∞ (fun p => fderiv ℝ velocity (v p)
      (p.2.2.1+cross (velocity (v p)) p.2.2.2)) :=
    (((contDiff_velocity (k:=∞)).fderiv_right (by simp)).comp hv).clm_apply
      (contDiff_snd.snd.fst.add (contDiff_cross.comp (hu.prodMk contDiff_snd.snd.snd)))
  have hD : ContDiff ℝ ∞ (fun p => 1-dot p.1.2.1 (velocity (v p))) :=
    contDiff_const.sub (contDiff_dot_pair.comp (hn.prodMk hu))
  have hR := ((smoothReciprocal_smooth hδ).comp hD).pow 3
  exact (contDiff_snd.fst.mul hD).smul
    ((((contDiff_const.sub (contDiff_dot_pair.comp (hu.prodMk hu))).mul hR).smul (hn.sub hu)).add
      ((contDiff_fst.fst.mul hR).smul
        (((contDiff_dot_pair.comp (hn.prodMk hb)).smul (hn.sub hu)).sub (hD.smul hb))))

lemma smoothNormalisedPhysical_eq {δ : ℝ} (hδ : 0 < δ)
    (p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)) (hp : δ ≤ 1-dot p.1.2.1 (velocity p.1.2.2)) :
    smoothNormalisedPhysical δ p=normalisedPhysicalIntegrand p := by
  simp only [smoothNormalisedPhysical,smoothReciprocal_eq hδ hp,normalisedPhysicalIntegrand,
    normalisedElectricKernel,div_eq_mul_inv,inv_pow]

attribute [local instance] Measure.Subtype.measureSpace

variable (t P : ℝ)
local instance instCompactSpaceElemVecSphere : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
local instance instCompactSpaceElemRealIccOfNat_solutions : CompactSpace (Icc (0:ℝ) t) := isCompact_iff_compactSpace.mp isCompact_Icc
local instance instCompactSpaceElemVecClosedBallOfNat : CompactSpace (closedBall (0:Vec) P) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
local instance instIsFiniteMeasureElemRealIccOfNatVolume_solutions : IsFiniteMeasure (volume : Measure (Icc (0:ℝ) t)) := ⟨by
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top⟩
local instance instIsFiniteMeasureElemVecClosedBallOfNatVolume : IsFiniteMeasure (volume : Measure (closedBall (0:Vec) P)) := ⟨by
  rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
  exact (isCompact_closedBall _ _).measure_lt_top⟩

lemma compactPolarIntegral_eq (G : (ℝ × Vec × Vec) × Vec → Vec)
    (hG : Continuous G) (x : Vec) :
    compactPolarIntegral t P G x = ∫ n : Sphere, ∫ r in Icc (0:ℝ) t,
      ∫ v in closedBall (0:Vec) P, G ((r,n.1,v),x) ∂volume ∂volume ∂sphereMeasure := by
  have hcont : Continuous (fun p : ConeParameters t P => G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),x)) :=
    hG.comp (((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).prodMk continuous_const)
  unfold compactPolarIntegral coneParameterMeasure
  rw [integral_prod _ (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    have hc : Continuous (fun p : Icc (0:ℝ) t × closedBall (0:Vec) P => G (((p.1:ℝ),n.1,(p.2:Vec)),x)) :=
      hG.comp (((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk continuous_const)
    try dsimp only at *
    rw [integral_prod _ (μ:=volume) (ν:=volume) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    dsimp only
    have hv (r : ℝ) : (∫ v : closedBall (0:Vec) P, G ((r,n.1,(v:Vec)),x)) =
        ∫ v in closedBall (0:Vec) P, G ((r,n.1,v),x) :=
      integral_subtype measurableSet_closedBall (fun v => G ((r,n.1,v),x))
    simp_rw [hv]
    exact integral_subtype measurableSet_Icc (fun r => ∫ v in closedBall (0:Vec) P, G ((r,n.1,v),x)))

lemma compactPolarIntegral_smooth (G : (ℝ × Vec × Vec) × Vec → Vec)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (compactPolarIntegral t P G) := by
  apply contDiff_integral_smoothFamily
  exact SmoothCompactFamily.ofJoint hG
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

end

lemma normalisedRetardedExtension_smooth {δ : ℝ} (hδ : 0<δ) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (t : ℝ) :
    ContDiff ℝ ∞ (normalisedRetardedExtension δ s t) := by
  have hr : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => p.1.1) := contDiff_fst.fst
  have hn : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => p.1.2.1) := contDiff_fst.snd.fst
  have hv : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => p.1.2.2) := contDiff_fst.snd.snd
  have hx := contDiff_snd.sub (hr.smul hn)
  have htime := (contDiff_const (c:=t)).sub hr
  exact (smoothNormalisedPhysical_smooth hδ).comp (contDiff_fst.prodMk
    ((hf.comp (htime.prodMk (hx.prodMk hv))).prodMk
      ((hE.comp (htime.prodMk hx)).prodMk (hB.comp (htime.prodMk hx)))))

lemma retardedElectricDensity_polar_integral {s : Solution} {t P δ r : ℝ}
    (hδ : 0<δ) (hr : 0 < r) (hrt : r≤t)
    (hden : ∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v))
    (hsupport : ∀ u∈Icc (0:ℝ) t, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0)
    (x : Vec) (n : Sphere) :
    r^2 • retardedElectricDensity s t x (x-r • n.1) =
      ∫ v in closedBall (0:Vec) P, normalisedRetardedExtension δ s t ((r,n.1,v),x) := by
  rw [retardedElectricDensity,coneRadius_sub_smul x n hr,coneDirection_sub_smul x n hr,
    ← integral_smul]
  have hrest : (∫ v in closedBall (0:Vec) P,
      r^2 • ((s.f (t-r,(x-r • n.1,v))*(1-dot n.1 (velocity v))) •
        physicalElectricKernel r n.1 (velocity v)
          (fderiv ℝ velocity v (s.E (t-r,x-r • n.1)+cross (velocity v) (s.B (t-r,x-r • n.1)))))) =
      ∫ v : Vec, r^2 • ((s.f (t-r,(x-r • n.1,v))*(1-dot n.1 (velocity v))) •
        physicalElectricKernel r n.1 (velocity v)
          (fderiv ℝ velocity v (s.E (t-r,x-r • n.1)+cross (velocity v) (s.B (t-r,x-r • n.1))))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hsupport (t-r) ⟨by linarith,by linarith⟩ _ v
      (by simpa only [mem_closedBall_zero_iff,not_le] using hv),zero_mul,zero_smul,smul_zero]
  rw [← hrest]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro v hv
  dsimp only [normalisedRetardedExtension]
  rw [smoothNormalisedPhysical_eq hδ _ (hden n.1 v (sphere_norm n) (mem_closedBall_zero_iff.mp hv)),
    normalisedPhysicalIntegrand_eq hr.ne']

lemma retardedElectricDensity_polar_compact {s : Solution} (hf : ContDiff ℝ ∞ s.f)
    (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (hc : CompactOnFiniteHorizons s)
    {t P δ : ℝ} (ht : 0≤t) (hδ : 0<δ)
    (hden : ∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v))
    (hsupport : ∀ r∈Icc (0:ℝ) t, ∀ x v, P<‖v‖ → s.f (r,(x,v))=0) :
    (fun x => ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) =
      compactPolarIntegral t P (normalisedRetardedExtension δ s t) := by
  funext x
  rw [integral_ball_polar_flip (integrableOn_retardedElectricDensity_le
    (hf.of_le (by simp)).contDiffOn (hE.of_le (by simp)).contDiffOn
    (hB.of_le (by simp)).contDiffOn hc ht le_rfl x),
    compactPolarIntegral_eq t P _ (normalisedRetardedExtension_smooth hδ hf hE hB t).continuous]
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have he : x+-(r • n.1)=x-r • n.1 := by module
    dsimp only
    rw [he]
    exact retardedElectricDensity_polar_integral hδ hr.1 hr.2.le hden hsupport x n)

lemma retardedMagneticDensity_polar_compact {s : Solution} (hf : ContDiff ℝ ∞ s.f)
    (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (hc : CompactOnFiniteHorizons s)
    {t P δ : ℝ} (ht : 0≤t) (hδ : 0<δ)
    (hden : ∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v))
    (hsupport : ∀ r∈Icc (0:ℝ) t, ∀ x v, P<‖v‖ → s.f (r,(x,v))=0) :
    (fun x => ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) =
      compactPolarIntegral t P (fun p => cross p.1.2.1 (normalisedRetardedExtension δ s t p)) := by
  have hG := normalisedRetardedExtension_smooth hδ hf hE hB t
  have hGB : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec =>
      cross p.1.2.1 (normalisedRetardedExtension δ s t p)) := contDiff_cross.comp (contDiff_fst.snd.fst.prodMk hG)
  funext x
  rw [integral_ball_polar_flip (integrableOn_retardedMagneticDensity_le
    (hf.of_le (by simp)).contDiffOn (hE.of_le (by simp)).contDiffOn
    (hB.of_le (by simp)).contDiffOn hc ht le_rfl x),compactPolarIntegral_eq t P _ hGB.continuous]
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have he : x+-(r • n.1)=x-r • n.1 := by module
    dsimp only
    rw [he,retardedMagneticDensity,coneDirection_sub_smul x n hr.1,←cross_smul_right,
      retardedElectricDensity_polar_integral hδ hr.1 hr.2.le hden hsupport x n]
    have hint : IntegrableOn (fun v : Vec => normalisedRetardedExtension δ s t ((r,n.1,v),x))
        (closedBall (0:Vec) P) :=
      (hG.continuous.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).prodMk
        continuous_const)).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    exact ((crossCLM n.1).integral_comp_comm hint).symm)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_BoundaryJets
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

section
universe u v

lemma norm_iteratedFDeriv_add_le {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => f y+g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (i:=n) (x:=x) ((hf.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact norm_add_le _ _

end

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_MixedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma retarded_density_spatial_smooth {s : Solution} (hf : ContDiff ℝ ∞ s.f)
    (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (hc : CompactOnFiniteHorizons s)
    {t P : ℝ} (ht : 0≤t)
    (hsupport : ∀ u∈Icc (0:ℝ) t, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) :
    ContDiff ℝ ∞ (fun x => ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) ∧
    ContDiff ℝ ∞ (fun x => ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) := by
  obtain ⟨δ,hδ,hden⟩ := uniform_cone_denominator P
  have hG := normalisedRetardedExtension_smooth hδ hf hE hB t
  rw [retardedElectricDensity_polar_compact hf hE hB hc ht hδ hden hsupport,
    retardedMagneticDensity_polar_compact hf hE hB hc ht hδ hden hsupport]
  exact ⟨compactPolarIntegral_smooth t P _ hG,compactPolarIntegral_smooth t P _
    (contDiff_cross.comp (contDiff_fst.snd.fst.prodMk hG))⟩

lemma norm_iteratedFDeriv_const_smul {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (c : ℝ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => c • f y) x‖=‖c‖*‖iteratedFDeriv ℝ n f x‖ := by
  rw [iteratedFDeriv_const_smul_apply' ((hf.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul]

lemma mixed_fields_derivative_tame {d : Datum} (hd : Admissible d)
    (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ D C : ℝ, 0≤D ∧ 0≤C ∧
      (∀ x, ‖iteratedFDeriv ℝ (k+1) d.E₀ x‖≤D ∧ ‖iteratedFDeriv ℝ (k+1) d.B₀ x‖≤D) ∧
      ∀ (s : Solution) (E B : Field), PicardRegular d s →
      ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → TransportFor s E B →
      ∀ T : ℝ, T≤1 →
      (∀ u∈Icc (0:ℝ) T, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) →
      ParticleJetBound k T A s.f → SpatialJetBound k T A E B →
      ∀ H : ℝ → ℝ, Continuous H → (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (t,y)) x‖≤D+C*(∫ u in Icc (0:ℝ) t, 1+H u) ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (t,y)) x‖≤D+C*(∫ u in Icc (0:ℝ) t, 1+H u) := by
  obtain ⟨D,hD,hinit,hbd⟩ := datum_boundary_global_jets hd (k+1)
  obtain ⟨K,hK,hcone⟩ := physical_cone_derivative_tame k hk P A hA
  refine ⟨D,(4*Real.pi)⁻¹*K,hD,by positivity,hinit,?_⟩
  intro s E B hs hE hB hV T hT hsupport hfj hEBj H hH hHpos hft hEBt t ht x
  by_cases ht0 : t=0
  · subst t
    have hEs : (fun y => s.E (0,y))=d.E₀ := funext hs.initial_E
    have hBs : (fun y => s.B (0,y))=d.B₀ := funext hs.initial_B
    simpa [hEs,hBs] using hinit x
  have htpos : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let q : Solution := {s with E:=E,B:=B}
  have hbound := hcone q hs.smooth_f hE hB hs.compact T hT hsupport hfj hEBj H hH hHpos hft hEBt t ht x
  have hsmooth := retarded_density_spatial_smooth (s:=q) hs.smooth_f hE hB hs.compact ht.1
    (fun u hu => hsupport u ⟨hu.1,hu.2.trans ht.2⟩)
  have hboundary := hbd t ⟨htpos,ht.2.trans hT⟩
  have he (y : Vec) := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell htpos y
  have heq : (fun y => s.E (t,y))=(fun y => electricBoundaryField (datumBoundarySolution d) t y+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity q t y (y+z)) := by
    funext y; rw [(he y).1,(hs.boundary_eq htpos y).1]
  have hbq : (fun y => s.B (t,y))=(fun y => magneticBoundaryField (datumBoundarySolution d) t y+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity q t y (y+z)) := by
    funext y; rw [(he y).2,(hs.boundary_eq htpos y).2]
  rw [heq,hbq]
  constructor
  · apply (norm_iteratedFDeriv_add_le hboundary.1.1 (hsmooth.1.const_smul _) (k+1) x).trans
    rw [norm_iteratedFDeriv_const_smul hsmooth.1,Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (add_le_add (hboundary.2 x).1 (mul_le_mul_of_nonneg_left hbound.1 (by positivity))).trans_eq (by ring)
  · apply (norm_iteratedFDeriv_add_le hboundary.1.2 (hsmooth.2.const_smul _) (k+1) x).trans
    rw [norm_iteratedFDeriv_const_smul hsmooth.2,Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (add_le_add (hboundary.2 x).2 (mul_le_mul_of_nonneg_left hbound.2 (by positivity))).trans_eq (by ring)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_VolterraMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma exists_tame_volterra_majorant {D C F : ℝ} (hD : 0≤D) (hC : 0≤C) (hF : 0≤F) :
    ∃ H : ℝ → ℝ, Continuous H ∧ Monotone H ∧ (∀ t, 0≤t → 1≤H t) ∧
      ∀ t, 0≤t → D+C*(∫ u in Icc (0:ℝ) t, 1+(F+1)*(1+H u))≤H t := by
  let ell := 2*C*(F+2)+1
  let H : ℝ → ℝ := fun t => (D+1)*Real.exp (ell*t)
  have hell : 0≤ell := by dsimp [ell]; positivity
  have hH : Continuous H := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hmon : Monotone H := fun a b hab => mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hell)) (by positivity)
  have hH1 (t : ℝ) (ht : 0≤t) : 1≤H t := by
    have h0 : H 0=D+1 := by simp [H]
    have hh := hmon ht
    rw [h0] at hh
    linarith
  have hd (t : ℝ) : HasDerivAt H (ell*H t) t := by
    have h1 := (((Real.hasDerivAt_exp (ell*t)).comp t ((hasDerivAt_id t).const_mul ell)).const_mul (D+1))
    refine h1.congr_deriv ?_
    simp only [H, Function.comp]
    ring
  refine ⟨H,hH,hmon,hH1,?_⟩
  intro t ht
  have hb (u : ℝ) (hu : 0≤u) : C*(1+(F+1)*(1+H u))≤ell*H u := by
    have h1 := hH1 u hu
    have hfirst : 1+(F+1)*(1+H u)≤(F+2)*(1+H u) := by linarith
    have hsecond : (F+2)*(1+H u)≤2*(F+2)*H u := by nlinarith [mul_nonneg (by linarith : 0≤F+2) (by linarith : 0≤H u-1)]
    calc
      C*(1+(F+1)*(1+H u))≤C*(2*(F+2)*H u) := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) hC
      _ ≤ ell*H u := by dsimp [ell]; nlinarith
  have hleft : Continuous (fun u => C*(1+(F+1)*(1+H u))) := by fun_prop
  have hright : Continuous (fun u => ell*H u) := continuous_const.mul hH
  have hi := setIntegral_mono_on (μ:=volume) (hleft.continuousOn.integrableOn_compact isCompact_Icc)
    (hright.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
    (fun u (hu : u∈Icc (0:ℝ) t) => hb u hu.1)
  have he : (∫ u in Icc (0:ℝ) t, ell*H u)=H t-(D+1) := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hright.intervalIntegrable 0 t)]
    simp [H]
  rw [integral_const_mul,he] at hi
  linarith

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardCurvature
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

lemma FieldControl.spatialJetBound_one {E B : Field} {T L N : ℝ}
    (hc : FieldControl T L N E B) (hN : 0≤N) :
    SpatialJetBound 1 T (max L N) E B := by
  intro t ht x i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
  · simpa only [norm_iteratedFDeriv_zero] using
      And.intro ((hc.1 t ht x).1.trans (le_max_left _ _)) ((hc.1 t ht x).2.trans (le_max_left _ _))
  · simp only [norm_iteratedFDeriv_one]
    have he : ‖fderiv ℝ (fun y => E (t,y)) x‖≤N := by
      apply norm_fderiv_le_of_lip' ℝ hN
      exact Eventually.of_forall fun y => (hc.2 t ht x y).1
    have hb : ‖fderiv ℝ (fun y => B (t,y)) x‖≤N := by
      apply norm_fderiv_le_of_lip' ℝ hN
      exact Eventually.of_forall fun y => (hc.2 t ht x y).2
    exact ⟨he.trans (le_max_right _ _),hb.trans (le_max_right _ _)⟩

lemma particleJetBound_one {f : Particle} {T A R P M : ℝ}
    (hb : LocalParticleBound T A R P f) (hl : PhaseParticleLip T M f) (hM : 0≤M) :
    ParticleJetBound 1 T (max A M) f := by
  intro t ht i hi z
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
  · simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using (hb t ht z.1 z.2).1.trans (le_max_left _ _)
  · rw [norm_iteratedFDeriv_one]
    apply le_trans _ (le_max_right A M)
    apply norm_fderiv_le_of_lip' ℝ hM
    exact Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hl t ht w z

theorem uniform_picard_sequence_jets_oai {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T A R P L N M : ℝ} (_ : 0<T) (hT1 : T≤1)
    (hN : 0≤N) (hM : 0≤M) (h0 : S 0=datumBoundarySolution d)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) :
    ∀ k : ℕ, ∃ Q : ℝ, 1≤Q ∧
      (∀ n, SpatialJetBound (k+1) T Q (S n).E (S n).B) ∧
      ∀ n, ParticleJetBound (k+1) T Q (S (n+1)).f := by
  intro k
  induction k with
  | zero =>
    let Q := max (max L N) (max (max A M) 1)
    have he : max L N≤Q := le_max_left _ _
    have hf : max A M≤Q := (le_max_left _ _).trans (le_max_right _ _)
    refine ⟨Q,(le_max_right _ _).trans (le_max_right _ _),?_,?_⟩
    · intro n t ht x i hi
      exact ⟨((hc n).spatialJetBound_one hN t ht x i hi).1.trans he,
        ((hc n).spatialJetBound_one hN t ht x i hi).2.trans he⟩
    · intro n t ht i hi z
      exact (particleJetBound_one (hr n).2.2.1 (hr n).2.2.2 hM t ht i hi z).trans hf
  | succ k ih =>
    obtain ⟨Q,hQ,hfields,hparticles⟩ := ih
    obtain ⟨F,hF,htransport⟩ := transported_derivative_tame hd (k+1) (by omega) Q hQ
    obtain ⟨D,C,hD,hC,hinit,hstep⟩ := mixed_fields_derivative_tame hd (k+1) (by omega) P Q hQ
    obtain ⟨H,hH,hHmon,hH1,hHstep⟩ := exists_tame_volterra_majorant hD hC hF
    have hHpos (t : ℝ) (ht : 0≤t) : 0≤H t := zero_le_one.trans (hH1 t ht)
    have hH0 : D≤H 0 := by simpa using hHstep 0 le_rfl
    let J : ℝ → ℝ := fun u => (F+1)*(1+H u)
    have hJ : Continuous J := continuous_const.mul (continuous_const.add hH)
    have hHJ (u : ℝ) (hu : 0≤u) : H u≤J u := by
      dsimp [J]
      nlinarith [mul_nonneg hF (hHpos u hu)]
    have hparticle (n : ℕ)
        (hold : ∀ t∈Icc (0:ℝ) T, ∀ x,
          ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).E (t,y)) x‖≤H t ∧
          ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).B (t,y)) x‖≤H t) :
        ∀ t∈Icc (0:ℝ) T, ∀ z,
          ‖iteratedFDeriv ℝ (k+1+1) (fun w => (S (n+1)).f (t,w)) z‖≤F*(1+H t) := by
      intro t ht z
      exact htransport (S n).E (S n).B (hsm n).1 (hsm n).2 (S (n+1)) (hr n).1 (hr n).2.1
        t ⟨ht.1,ht.2.trans hT1⟩ (fun u hu => hfields n u ⟨hu.1,hu.2.trans ht.2⟩)
        (H t) (hHpos t ht.1) (fun u hu x => ⟨(hold u ⟨hu.1,hu.2.trans ht.2⟩ x).1.trans (hHmon hu.2),
          (hold u ⟨hu.1,hu.2.trans ht.2⟩ x).2.trans (hHmon hu.2)⟩) t ⟨ht.1,le_rfl⟩ z
    have htop : ∀ n, ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).E (t,y)) x‖≤H t ∧
        ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).B (t,y)) x‖≤H t := by
      intro n
      induction n with
      | zero =>
        intro t ht x
        simpa only [h0,datumBoundarySolution] using
          And.intro ((hinit x).1.trans (hH0.trans (hHmon ht.1))) ((hinit x).2.trans (hH0.trans (hHmon ht.1)))
      | succ n ihn =>
        have hf := hparticle n ihn
        intro t ht x
        have hh := hstep (S (n+1)) (S n).E (S n).B (hr n).1 (hsm n).1 (hsm n).2 (hr n).2.1 T hT1
          (fun u hu y v hv => by
            by_contra hn
            exact (not_le_of_gt hv) (((hr n).2.2.1 u hu y v).2 hn).2)
          (hparticles n) (hfields n) J hJ (fun u hu => (hHpos u hu.1).trans (hHJ u hu.1))
          (fun u hu z => (hf u hu z).trans (by dsimp [J]; nlinarith [hHpos u hu.1]))
          (fun u hu y => ⟨(ihn u hu y).1.trans (hHJ u hu.1),(ihn u hu y).2.trans (hHJ u hu.1)⟩) t ht x
        exact ⟨hh.1.trans (hHstep t ht.1),hh.2.trans (hHstep t ht.1)⟩
    let B := Q+H 1+F*(1+H 1)
    have hHB : H 1≤B := by dsimp [B]; nlinarith [hHpos 1 zero_le_one]
    have hQB : Q≤B := by dsimp [B]; nlinarith [hHpos 1 zero_le_one]
    have hFB : F*(1+H 1)≤B := by dsimp [B]; linarith [hHpos 1 zero_le_one]
    refine ⟨B,hQ.trans hQB,?_,?_⟩
    · intro n t ht x i hi
      by_cases hik : i≤k+1
      · exact ⟨(hfields n t ht x i hik).1.trans hQB,(hfields n t ht x i hik).2.trans hQB⟩
      · have he : i=k+1+1 := by omega
        subst i
        exact ⟨(htop n t ht x).1.trans ((hHmon (ht.2.trans hT1)).trans hHB),
          (htop n t ht x).2.trans ((hHmon (ht.2.trans hT1)).trans hHB)⟩
    · intro n t ht i hi z
      by_cases hik : i≤k+1
      · exact (hparticles n t ht i hik z).trans hQB
      · have he : i=k+1+1 := by omega
        subst i
        exact (hparticle n (htop n) t ht z).trans
          ((mul_le_mul_of_nonneg_left (add_le_add_right (hHmon (ht.2.trans hT1)) 1) hF).trans hFB)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.uniform_picard_sequence_jets_oai := @OAI.RVM.uniform_picard_sequence_jets_oai
