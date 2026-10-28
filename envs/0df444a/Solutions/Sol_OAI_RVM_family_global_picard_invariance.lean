-- Prove2me | solution 1 for OAI.RVM.family_global_picard_invariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:26:36.573529+00:00
-- url     : https://prove2.me/submissions/e7660045-a1ab-4de4-8811-4a66d92a4b09

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_exists_smoothLorentzFlow
import Theorems.Thm_OAI_RVM_mixed_electric_physical_representation
import Theorems.Thm_OAI_RVM_mixed_magnetic_physical_representation

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

lemma integral_ball_norm_rpow_neg {α R : ℝ} (hα : α<3) (hR : 0≤R) :
    (∫ z in ball (0:Vec) R, ‖z‖ ^ (-α)) =
      (4*Real.pi) * R^(3-α)/(3-α) := by
  rw [← integral_indicator measurableSet_ball,
    integral_polar ((integrableOn_norm_rpow_neg hα).integrable_indicator measurableSet_ball)]
  have he (n : Sphere) :
      (∫ r in Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator
        (fun z => ‖z‖^(-α)) (r • n.1)) = R^(3-α)/(3-α) := by
    have heq : ∀ r ∈ Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator
        (fun z => ‖z‖^(-α)) (r • n.1) =
        (Ioo (0:ℝ) R).indicator (fun r => r^(2-α)) r := by
      intro r hr
      change 0 < r at hr
      have hn : ‖r • n.1‖=r := by simp [norm_smul,abs_of_pos hr]
      by_cases h : r<R
      · rw [indicator_of_mem (show r • n.1 ∈ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using h),
          indicator_of_mem (show r ∈ Ioo (0:ℝ) R from ⟨hr,h⟩),hn,smul_eq_mul]
        rw [← Real.rpow_two,← Real.rpow_add hr]
        congr 1
      · rw [indicator_of_notMem (show r • n.1 ∉ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using h),
          indicator_of_notMem (show r ∉ Ioo (0:ℝ) R from fun hh => h hh.2),smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq,setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR,integral_rpow (Or.inl (by linarith : -1<2-α))]
    have hne : 2-α+1≠0 := by linarith
    rw [Real.zero_rpow hne,sub_zero]
    rw [show 2-α+1=3-α by ring]
  simp_rw [he]
  rw [integral_const,smul_eq_mul,sphere_area]
  ring

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

lemma uniform_normalised_physical_kernel (P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C := by
  let K : Set (ℝ × Vec × Vec × Vec × Vec) :=
    Icc 0 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P ×ˢ
      closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  let r : (ℝ × Vec × Vec × Vec × Vec) → ℝ := Prod.fst
  let n : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.1
  let v : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.1
  let E : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.1
  let B : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.2
  have hr : Continuous r := continuous_fst
  have hn : Continuous n := continuous_snd.fst
  have hv : Continuous v := continuous_snd.snd.fst
  have hE : Continuous E := continuous_snd.snd.snd.fst
  have hB : Continuous B := continuous_snd.snd.snd.snd
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha : Continuous (fun p => fderiv ℝ velocity (v p) (E p+cross (velocity (v p)) (B p))) :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp hv).clm_apply
      (hE.add ((contDiff_cross (k:=1)).continuous.comp (hu.prodMk hB)))
  have hd : Continuous (fun p => 1-dot (n p) (velocity (v p))) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hk := hd.continuousOn.smul (continuousOn_normalisedElectricKernel
    hr.continuousOn hn.continuousOn hu.continuousOn ha.continuousOn (S:=K) (by
      intro p hp
      exact (cone_denom_pos (v p) (n p) (by simpa only [n,mem_sphere,dist_zero_right] using hp.2.1)).ne'))
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hk).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro r hr n hn v hv E B hE hB
  apply le_trans (hC _ ⟨(r,n,v,E,B),?_,rfl⟩) (le_max_right _ _)
  exact ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall_zero_iff] using hv,
    by simpa only [mem_closedBall_zero_iff] using hE,
    by simpa only [mem_closedBall_zero_iff] using hB⟩

lemma uniform_physical_kernel (P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C/r^2 := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_physical_kernel P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv E B hE hB
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv E B hE hB
  rw [normalisedElectricKernel_eq hr.1.ne',smul_comm (1-dot n (velocity v)),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma physical_integral_bound {A P C r : ℝ} {n E B : Vec} {f : Vec → ℝ}
    (hA : 0≤A)
    (hbound : ∀ v : Vec, ‖v‖≤P →
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C/r^2)
    (hf : ∀ v, |f v|≤A) (hs : ∀ v, P<‖v‖ → f v=0) :
    ‖∫ v : Vec, (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤
      (A*C*volume.real (closedBall (0:Vec) P))/r^2 := by
  let g : Vec → Vec := fun v => (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
    (fderiv ℝ velocity v (E+cross (velocity v) B))
  have he : (∫ v in closedBall (0:Vec) P, g v)=∫ v, g v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hv' : P<‖v‖ := by simpa only [mem_closedBall_zero_iff,not_le] using hv
    simp [g,hs v hv']
  change ‖∫ v, g v‖≤_
  rw [← he]
  have hb : ∀ v∈closedBall (0:Vec) P, ‖g v‖≤A*(C/r^2) := by
    intro v hv
    have hv' : ‖v‖≤P := mem_closedBall_zero_iff.mp hv
    dsimp [g]
    rw [mul_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hf v) (hbound v hv') (norm_nonneg _) hA
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (isCompact_closedBall (0:Vec) P).measure_lt_top hb
  exact hh.trans_eq (by ring)

lemma uniform_retarded_density_bound (A P L : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ), T≤1 →
      (∀ t∈Icc 0 T, ∀ z, |s.f (t,z)|≤A) →
      (∀ t∈Icc 0 T, ∀ (x v : Vec), s.f (t,x,v)≠0 →
        ‖v‖≤P ∧ ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L) →
      ∀ t∈Icc 0 T, ∀ (x z : Vec), 0<‖z‖ → ‖z‖≤t →
        ‖retardedElectricDensity s t x (x+z)‖≤C/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)‖≤C/‖z‖^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_kernel P L
  refine ⟨A*K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro s T hT hf hs t ht x z hz hzt
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have he : ‖retardedElectricDensity s t x (x+z)‖≤
      (A*K*volume.real (closedBall (0:Vec) P))/‖z‖^2 := by
    by_cases hn : ∃ v : Vec, s.f (t-‖z‖,x+z,v)≠0
    · obtain ⟨v,hv⟩ := hn
      have hEB := hs _ htime _ v hv
      unfold retardedElectricDensity
      rw [coneRadius_add]
      apply physical_integral_bound hA
      · intro u hu
        exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ (coneDirection_norm hxy)
          u hu _ _ hEB.2.1 hEB.2.2
      · intro u
        exact hf _ htime (x+z,u)
      · intro u hu
        by_contra hnu
        exact (not_lt_of_ge (hs _ htime _ u hnu).1) hu
    · have hzero : ∀ v : Vec, s.f (t-‖z‖,x+z,v)=0 := by simpa using hn
      simp only [retardedElectricDensity,coneRadius_add,hzero,zero_mul,zero_smul,integral_zero,norm_zero]
      positivity
  refine ⟨he,?_⟩
  exact (norm_cross_le _ _).trans (by simpa only [coneDirection_norm hxy,one_mul] using he)

lemma kernel_tip_le_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : IntegrableOn F (ball (0:Vec) R))
    (hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖∫ z in ball (0:Vec) R, F z‖≤4*Real.pi*C*R := by
  have hbound : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C*‖z‖^(-(2:ℝ)) := by
    simpa only [Real.rpow_neg (norm_nonneg _),Real.rpow_two,div_eq_mul_inv] using hb
  have hi := integrableOn_norm_rpow_neg (R:=R) (by norm_num : (2:ℝ)<3)
  calc
    _ ≤ ∫ z in ball (0:Vec) R, ‖F z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in ball (0:Vec) R, C*‖z‖^(-(2:ℝ)) := integral_mono_ae hF.norm (hi.const_mul C) hbound
    _ = 4*Real.pi*C*R := by
      rw [integral_const_mul,integral_ball_norm_rpow_neg (by norm_num : (2:ℝ)<3) hR]
      norm_num only [show (3:ℝ)-2=1 by norm_num,Real.rpow_one,div_one]
      ring

namespace SmoothLorentzFlow

lemma spatial_travel_bound {E B : Field} (F : SmoothLorentzFlow E B) (z : Phase)
    {T t : ℝ} (ht : t∈Icc 0 T) : ‖(F.forward z t).1-z.1‖≤t := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=fun r => (F.forward z r).1) (f':=fun r => velocity (F.forward z r).2)
    (fun r (_ : r∈Icc 0 T) => ((ContinuousLinearMap.fst ℝ Vec Vec).hasFDerivAt.comp_hasDerivAt r (F.ode z r)).hasDerivWithinAt)
    (fun r (_ : r∈Ico 0 T) => (norm_velocity_lt_one _).le) t ht
  simpa only [F.initial,one_mul,sub_zero] using hh

lemma momentum_travel_bound {E B : Field} (F : SmoothLorentzFlow E B) (z : Phase)
    {T t R L : ℝ} (ht : t∈Icc 0 T) (hz : ‖z.1‖+T≤R)
    (_hL : 0≤L) (hE : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖E (r,x)‖≤L)
    (hB : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖B (r,x)‖≤L) :
    ‖(F.forward z t).2-z.2‖≤(2*L)*t := by
  have hspace (r : ℝ) (hr : r∈Icc 0 T) : ‖(F.forward z r).1‖≤R := by
    calc
      _ ≤ ‖(F.forward z r).1-z.1‖+‖z.1‖ := norm_le_norm_sub_add _ _
      _ ≤ r+‖z.1‖ := add_le_add (F.spatial_travel_bound z hr) le_rfl
      _ ≤ R := by linarith [hr.2]
  have hb (r : ℝ) (hr : r∈Ico 0 T) :
      ‖E (r,(F.forward z r).1)+cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1))‖≤2*L := by
    have hh := Ico_subset_Icc_self hr
    calc
      _ ≤ ‖E (r,(F.forward z r).1)‖+‖cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1))‖ := norm_add_le _ _
      _ ≤ L + 1*L := add_le_add (hE r hh _ (hspace r hh))
        ((norm_cross_le _ _).trans (mul_le_mul (norm_velocity_lt_one _).le
          (hB r hh _ (hspace r hh)) (norm_nonneg _) (by norm_num)))
      _ = 2*L := by ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=fun r => (F.forward z r).2)
    (f':=fun r => E (r,(F.forward z r).1)+cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1)))
    (fun r (_ : r∈Icc 0 T) => ((ContinuousLinearMap.snd ℝ Vec Vec).hasFDerivAt.comp_hasDerivAt r (F.ode z r)).hasDerivWithinAt) hb t ht
  simpa only [F.initial,sub_zero] using hh

lemma transport_for {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,F.forward z t)=s.f (0,z) := by
  have hd (r : ℝ) : HasDerivAt (fun r => s.f (r,F.forward z r)) (0:ℝ) r := by
    have hh := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (F.ode z r))
    change HasDerivAt (fun r => s.f (r,F.forward z r))
      (fderiv ℝ s.f (r,F.forward z r) (1,lorentzField E B (r,F.forward z r))) r at hh
    rw [hV] at hh
    exact hh
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [F.initial] using he

lemma transport_for_inverse {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,z)=s.f (0,F.backward (t,z)) := by
  simpa only [F.right_inverse] using F.transport_for hf hV t (F.backward (t,z))

lemma transported_sup_bound {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) {A : ℝ}
    (hA : ∀ z, |s.f (0,z)|≤A) (t : ℝ) (z : Phase) : |s.f (t,z)|≤A := by
  rw [F.transport_for_inverse hf hV]
  exact hA _

lemma transported_phase_bound {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) {R₀ P₀ T L t : ℝ}
    (h₀ : ∀ z : Phase, s.f (0,z)≠0 → ‖z.1‖≤R₀ ∧ ‖z.2‖≤P₀)
    (hL : 0≤L) (hE : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R₀+T → ‖E (r,x)‖≤L)
    (hB : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R₀+T → ‖B (r,x)‖≤L)
    (ht : t∈Icc 0 T) (z : Phase) (hz : s.f (t,z)≠0) :
    ‖z.1‖≤R₀+t ∧ ‖z.2‖≤P₀+2*L*t := by
  let z₀ := F.backward (t,z)
  have he : F.forward z₀ t=z := F.right_inverse t z
  have hz₀ : s.f (0,z₀)≠0 := by
    rw [← F.transport_for_inverse hf hV]
    exact hz
  have hb := h₀ z₀ hz₀
  have hx := F.spatial_travel_bound z₀ ht
  have hv := F.momentum_travel_bound z₀ ht (by linarith [hb.1]) hL hE hB
  rw [he] at hx hv
  constructor
  · exact (norm_le_norm_sub_add z.1 z₀.1).trans (by linarith [hb.1])
  · exact (norm_le_norm_sub_add z.2 z₀.2).trans (by linarith [hb.2])

end SmoothLorentzFlow

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

lemma scaled_kernel_tip_le_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : IntegrableOn F (ball (0:Vec) R))
    (hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) R, F z‖≤C*R := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹)]
  calc
    _ ≤ (4*Real.pi)⁻¹*(4*Real.pi*C*R) :=
      mul_le_mul_of_nonneg_left (kernel_tip_le_on hR hF hb) (by positivity)
    _ = C*R := by field_simp

lemma mixed_fields_bound {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t C D : ℝ} (ht : 0<t) (x : Vec)
    (hD : ‖electricBoundaryField s t x‖≤D ∧ ‖magneticBoundaryField s t x‖≤D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      ‖retardedElectricDensity {s with E:=E,B:=B} t x (x+z)‖≤C/‖z‖^2 ∧
      ‖retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)‖≤C/‖z‖^2) :
    ‖s.E (t,x)‖≤D+C*t ∧ ‖s.B (t,x)‖≤D+C*t := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  have he := mixed_physical_vector hf hE hB hE' hB' hc hV hρ hj hM ht x
  have hEe : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      retardedElectricDensity {s with E:=E,B:=B} t x (x+z)‖≤C*t := by
    apply scaled_kernel_tip_le_on ht.le
      (integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x)
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hden z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le).1
  have hBb : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)‖≤C*t := by
    apply scaled_kernel_tip_le_on ht.le
      (integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x)
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hden z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le).2
  constructor
  · rw [he.1]
    exact (norm_add_le _ _).trans (add_le_add hD.1 hEe)
  · rw [he.2]
    exact (norm_add_le _ _).trans (add_le_add hD.2 hBb)

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_StrongLocalExistence
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

theorem family_global_picard_invariance_oai {ι : Type*} {d : ι → Datum} (_ : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (_ : 0≤D₀) (_ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      (∀ i, GlobalFieldBound T L (fun p : ℝ × Vec => (d i).E₀ p.2) (fun p : ℝ × Vec => (d i).B₀ p.2) ∧
      ∀ U : ℝ, 0≤U → U≤T → ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → GlobalFieldBound U L E B →
        ∀ s : Solution, PicardRegular (d i) s → TransportFor s E B →
          LocalParticleBound U A R P s.f ∧ GlobalFieldBound U L s.E s.B) := by
  let R := R₀+1
  let P := P₀+1
  let L := D+1
  have hL : 0<L := by dsimp [L]; linarith
  obtain ⟨C,hC,hdensity⟩ := uniform_retarded_density_bound A P L hA
  let T := min 1 (min ((2*L+1)⁻¹) ((C+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1 := min_le_left _ _
  have hT2 : T≤(2*L+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hT3 : T≤(C+1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hLT : 2*L*T≤1 := by
    have hh : T*(2*L+1)≤1 := (le_div_iff₀ (by positivity : 0<2*L+1)).mp (by simpa only [one_div] using hT2)
    nlinarith
  have hCT : C*T≤1 := by
    have hh : T*(C+1)≤1 := (le_div_iff₀ (by positivity : 0<C+1)).mp (by simpa only [one_div] using hT3)
    nlinarith
  refine ⟨T,A,R,P,L,hT,hT1,hA,by dsimp [R]; linarith,by dsimp [P]; linarith,hL,?_⟩
  intro i
  have hf₀ := (hcaps i).particle
  have hphase₀ := (hcaps i).support
  have hDEB := (hcaps i).fields
  have hboundary := (hcaps i).boundary
  constructor
  · intro t ht x
    exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
      (hDEB x).2.trans (by dsimp [L]; linarith)⟩
  · intro U hU0 hU E B hE hB hEB s hs hV
    have hU1 : U≤1 := hU.trans hT1
    have hLU : 2*L*U≤1 := (mul_le_mul_of_nonneg_left hU (by positivity)).trans hLT
    have hCU : C*U≤1 := (mul_le_mul_of_nonneg_left hU hC).trans hCT
    obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
    have hf : ∀ t∈Icc 0 U, ∀ z, |s.f (t,z)|≤A := by
      intro t ht z
      exact F.transported_sup_bound hs.smooth_f hV (fun z => by rw [hs.initial_f]; exact hf₀ z) t z
    have hphase : ∀ t∈Icc 0 U, ∀ z : Phase, s.f (t,z)≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
      intro t ht z hz
      have hh := F.transported_phase_bound hs.smooth_f hV
        (R₀:=R₀) (P₀:=P₀) (T:=U) (L:=L)
        (fun z hz => hphase₀ z (by simpa only [hs.initial_f] using hz)) hL.le
        (fun r hr x hx => (hEB r hr x).1)
        (fun r hr x hx => (hEB r hr x).2) ht z hz
      constructor
      · dsimp [R]
        linarith [hh.1,ht.2]
      · dsimp [P]
        have hh' : 2*L*t≤2*L*U := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        linarith [hh.2]
    refine ⟨fun t ht x v => ⟨hf t ht (x,v),hphase t ht (x,v)⟩,?_⟩
    intro t ht x
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_B]
      exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
        (hDEB x).2.trans (by dsimp [L]; linarith)⟩
    · have hbd := hboundary t ⟨ht0,ht.2.trans hU1⟩ x
      rw [← (hs.boundary_eq ht0 x).1,← (hs.boundary_eq ht0 x).2] at hbd
      have hdens := hdensity {s with E:=E,B:=B} U hU1 hf (by
        intro r hr y v hv
        exact ⟨(hphase r hr (y,v) hv).2,hEB r hr y⟩) t ht x
      have hh := mixed_fields_bound hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
        hs.smooth_rho hs.smooth_current hs.maxwell ht0 x hbd hdens
      have hh' : C*t≤C*U := mul_le_mul_of_nonneg_left ht.2 hC
      have hbound : D+C*t≤L := by dsimp [L]; linarith
      exact ⟨hh.1.trans hbound,hh.2.trans hbound⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RVM.family_global_picard_invariance_oai.{u_1} := @OAI.RVM.family_global_picard_invariance_oai.{u_1}
