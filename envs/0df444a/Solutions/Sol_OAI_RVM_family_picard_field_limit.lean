-- Prove2me | solution 1 for OAI.RVM.family_picard_field_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:28:08.82914+00:00
-- url     : https://prove2.me/submissions/c042ced1-51c9-461e-bc18-d23e75ebaec5

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_exists_picard_regular
import Theorems.Thm_OAI_RVM_family_global_picard_invariance
import Theorems.Thm_OAI_RVM_mixed_electric_physical_representation
import Theorems.Thm_OAI_RVM_mixed_magnetic_physical_representation
import Theorems.Thm_OAI_RVM_transported_comparison
import Theorems.Thm_OAI_RVM_transported_spatial_lipschitz

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ShiftedRho
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coneDirection_add (x z : Vec) : coneDirection x (x+z)=-(‖z‖⁻¹ • z) := by
  unfold coneDirection
  rw [coneRadius_add,show x-(x+z) = -z by abel,smul_neg]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

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

lemma compact_parameter_lipschitz
    {U W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {K : Set U} {S : Set W} {g : U × W → Z}
    (hK : IsCompact K) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hg : ∀ q∈K ×ˢ S, ContDiffAt ℝ 1 g q) :
    ∃ C : ℝ, 0≤C ∧ ∀ p∈K, ∀ x∈S, ∀ y∈S, ‖g (p,y)-g (p,x)‖≤C*‖y-x‖ := by
  have hd : ContinuousOn (fderiv ℝ g) (K ×ˢ S) :=
    fun q hq => ((hg q hq).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨D,hD⟩ := ((hK.prod hS).image_of_continuousOn hd).isBounded.exists_norm_le
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro p hp x hx y hy
  apply hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by norm_num)).comp z
      ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z)).differentiableAt) _ hx hy
  intro z hz
  have hf := ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by norm_num)).hasFDerivAt.comp z
    ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z))
  rw [hf.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _)
  intro v
  change ‖fderiv ℝ g (p,z) (0,v)‖≤ max D 0*‖v‖
  have hh := (fderiv ℝ g (p,z)).le_opNorm (0,v)
  simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    ((hD _ ⟨(p,z),⟨hp,hz⟩,rfl⟩).trans (le_max_left _ _)) (norm_nonneg v))

lemma contDiffAt_normalisedElectricKernel {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {k : ℕ∞ω}
    {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => normalisedElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div (hD.pow 3) (pow_ne_zero 3 hd)).smul
      (hn.sub hu)).add ((hr.div (hD.pow 3) (pow_ne_zero 3 hd)).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma normalisedPhysicalIntegrand_smoothAt {p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)}
    (hd : 1-dot p.1.2.1 (velocity p.1.2.2)≠0) :
    ContDiffAt ℝ ∞ normalisedPhysicalIntegrand p := by
  let v : ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) → Vec := fun p => p.1.2.2
  have hv : ContDiff ℝ ∞ v := contDiff_fst.snd.snd
  have hu : ContDiff ℝ ∞ (fun p => velocity (v p)) := contDiff_velocity.comp hv
  have hb : ContDiff ℝ ∞ (fun p => fderiv ℝ velocity (v p)
      (p.2.2.1+cross (velocity (v p)) p.2.2.2)) :=
    (((contDiff_velocity (k:=∞)).fderiv_right (by simp)).comp hv).clm_apply
      (contDiff_snd.snd.fst.add (contDiff_cross.comp (hu.prodMk contDiff_snd.snd.snd)))
  have hD : ContDiff ℝ ∞ (fun p => 1-dot p.1.2.1 (velocity (v p))) :=
    contDiff_const.sub (contDiff_dot_pair.comp (contDiff_fst.snd.fst.prodMk hu))
  exact (contDiffAt_snd.fst.mul hD.contDiffAt).smul
    (contDiffAt_normalisedElectricKernel contDiffAt_fst.fst contDiffAt_fst.snd.fst
      hu.contDiffAt hb.contDiffAt hd)

lemma uniform_normalised_integrand_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a b : ℝ, |a|≤A → |b|≤A →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ‖normalisedPhysicalIntegrand ((r,n,v),(a,E,B))-
        normalisedPhysicalIntegrand ((r,n,v),(b,E',B'))‖≤
          C*max |a-b| (max ‖E-E'‖ ‖B-B'‖) := by
  let K : Set (ℝ × Vec × Vec) := Icc (0:ℝ) 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  let S : Set (ℝ × Vec × Vec) := closedBall (0:ℝ) A ×ˢ closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : Convex ℝ S := (convex_closedBall _ _).prod ((convex_closedBall _ _).prod (convex_closedBall _ _))
  obtain ⟨C,hC,hb⟩ := compact_parameter_lipschitz hK hS hc (g:=normalisedPhysicalIntegrand) (by
    intro p hp
    apply (normalisedPhysicalIntegrand_smoothAt ?_).of_le (by simp)
    exact (cone_denom_pos p.1.2.2 p.1.2.1
      (by simpa only [mem_sphere,dist_zero_right] using hp.1.2.1)).ne')
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  have hh := hb (r,n,v) ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
      by simpa only [mem_closedBall_zero_iff] using hv⟩
    (b,E',B') ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using hb',
      by simpa only [mem_closedBall_zero_iff] using hE',by simpa only [mem_closedBall_zero_iff] using hB'⟩
    (a,E,B) ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using ha,
      by simpa only [mem_closedBall_zero_iff] using hE,by simpa only [mem_closedBall_zero_iff] using hB⟩
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using hh

lemma normalisedPhysicalIntegrand_eq {r : ℝ} (hr : r≠0) (n v : Vec) (a : ℝ) (E B : Vec) :
    normalisedPhysicalIntegrand ((r,n,v),(a,E,B)) = r^2 •
      ((a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  simp only [normalisedPhysicalIntegrand,normalisedElectricKernel_eq hr]
  exact smul_comm _ _ _

lemma uniform_physical_integrand_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a b : ℝ, |a|≤A → |b|≤A →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ‖(a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B))-
        (b*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B'))‖≤
          (C/r^2)*max |a-b| (max ‖E-E'‖ ‖B-B'‖) := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_integrand_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  rw [normalisedPhysicalIntegrand_eq hr.1.ne',normalisedPhysicalIntegrand_eq hr.1.ne',
    ← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma integrable_physical_integrand {f : Vec → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {r : ℝ} (hr : r≠0) {n : Vec} (hn : ‖n‖=1) (E B : Vec) :
    Integrable (fun v : Vec => (f v*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hd : Continuous (fun v => 1-dot n (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  exact ((hf.mul hd).smul (continuous_physicalElectricKernel_velocity hr hn E B)).integrable_of_hasCompactSupport
    (hc.mul_right.smul_right)

lemma uniform_physical_integral_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ f g : Vec → ℝ, Continuous f → Continuous g → HasCompactSupport f → HasCompactSupport g →
      (∀ v, |f v|≤A ∧ |g v|≤A) → (∀ v, P<‖v‖ → f v=0 ∧ g v=0) →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ∀ D : ℝ, (∀ v, |f v-g v|≤D) → ‖E-E'‖≤D → ‖B-B'‖≤D →
      ‖(∫ v : Vec, (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B)))-
        (∫ v : Vec, (g v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B')))‖≤ C*D/r^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_integrand_lipschitz A P L
  refine ⟨K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro r hr n hn f g hf hg hfc hgc hab hs E B E' B' hE hB hE' hB' D hD hEd hBd
  rw [← integral_sub (integrable_physical_integrand hf hfc hr.1.ne' hn E B)
    (integrable_physical_integrand hg hgc hr.1.ne' hn E' B')]
  let H : Vec → Vec := fun v =>
    (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B))-
    (g v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B'))
  change ‖∫ v, H v‖≤_
  have he : (∫ v in closedBall (0:Vec) P, H v)=∫ v, H v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    obtain ⟨hvf,hvg⟩ := hs v (by simpa only [mem_closedBall_zero_iff,not_le] using hv)
    simp only [H,hvf,hvg,zero_mul,zero_smul,sub_self]
  rw [← he]
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (isCompact_closedBall (0:Vec) P).measure_lt_top (C:=(K/r^2)*D) (f:=H) (by
      intro v hv
      exact (hk r hr n hn v (mem_closedBall_zero_iff.mp hv) (f v) (g v) (hab v).1 (hab v).2
        E B E' B' hE hB hE' hB').trans
          (mul_le_mul_of_nonneg_left (max_le (hD v) (max_le hEd hBd)) (by positivity)))
  exact hh.trans_eq (by ring)

lemma uniform_retarded_density_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s s' : Solution) (T : ℝ), T≤1 →
      ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s'.f →
      CompactOnFiniteHorizons s → CompactOnFiniteHorizons s' →
      (∀ t∈Icc 0 T, ∀ x v, |s.f (t,x,v)|≤A ∧ |s'.f (t,x,v)|≤A) →
      (∀ t∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (t,x,v)=0 ∧ s'.f (t,x,v)=0) →
      (∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L ∧
        ‖s'.E (t,x)‖≤L ∧ ‖s'.B (t,x)‖≤L) →
      ∀ t∈Icc 0 T, ∀ x x' z : Vec, 0<‖z‖ → ‖z‖≤t → ∀ D : ℝ,
      (∀ v, |s.f (t-‖z‖,x+z,v)-s'.f (t-‖z‖,x'+z,v)|≤D) →
      ‖s.E (t-‖z‖,x+z)-s'.E (t-‖z‖,x'+z)‖≤D →
      ‖s.B (t-‖z‖,x+z)-s'.B (t-‖z‖,x'+z)‖≤D →
        ‖retardedElectricDensity s t x (x+z)-retardedElectricDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)-retardedMagneticDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 := by
  obtain ⟨C,hC,hk⟩ := uniform_physical_integral_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro s s' T hT hf hf' hc hc' hab hs hEB t ht x x' z hz hzt D hD hEd hBd
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have hn : ‖-(‖z‖⁻¹ • z)‖=1 := by simpa only [coneDirection_add] using coneDirection_norm hxy
  obtain ⟨hfc,hcomp⟩ := (show RegularParticle s.f from ⟨(hf.of_le (by simp)).contDiffOn,hc⟩).slice htime.1 (x+z)
  obtain ⟨hgc,hcomp'⟩ := (show RegularParticle s'.f from ⟨(hf'.of_le (by simp)).contDiffOn,hc'⟩).slice htime.1 (x'+z)
  have he : ‖retardedElectricDensity s t x (x+z)-retardedElectricDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 := by
    simp only [retardedElectricDensity,coneRadius_add,coneDirection_add]
    exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ hn _ _ hfc.continuous hgc.continuous hcomp hcomp'
      (fun v => ⟨(hab _ htime (x+z) v).1,(hab _ htime (x'+z) v).2⟩)
      (fun v hv => ⟨(hs _ htime (x+z) v hv).1,(hs _ htime (x'+z) v hv).2⟩)
      _ _ _ _ (hEB _ htime (x+z)).1 (hEB _ htime (x+z)).2.1
      (hEB _ htime (x'+z)).2.2.1 (hEB _ htime (x'+z)).2.2.2 D hD hEd hBd
  refine ⟨he,?_⟩
  simp only [retardedMagneticDensity,coneDirection_add,← cross_sub_right]
  exact (norm_cross_le _ _).trans (by simpa only [hn,one_mul] using he)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardContraction
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

lemma norm_boundary_integral_difference {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F G : Vec → W} {a b : W} {t C D : ℝ} (ht : 0≤t)
    (hF : IntegrableOn F (ball (0:Vec) t)) (hG : IntegrableOn G (ball (0:Vec) t))
    (hab : ‖a-b‖≤D)
    (hFG : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t → ‖F z-G z‖≤C/‖z‖^2) :
    ‖(a+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z)-
      (b+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, G z)‖≤D+C*t := by
  rw [show (a+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z)-
      (b+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, G z)=
      (a-b)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, (F z-G z) by
        rw [integral_sub hF hG,smul_sub]; abel]
  apply (norm_add_le _ _).trans (add_le_add hab ?_)
  apply scaled_kernel_tip_le_on ht (hF.sub hG)
  filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hFG z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le

lemma mixed_fields_difference_bound {d : Datum} {s s' : Solution} {E B E' B' : Field}
    (hs : PicardRegular d s) (hs' : PicardRegular d s')
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
    {t C D : ℝ} (ht : 0<t) (x x' : Vec)
    (hb : ‖electricBoundaryField (datumBoundarySolution d) t x-
        electricBoundaryField (datumBoundarySolution d) t x'‖≤D ∧
      ‖magneticBoundaryField (datumBoundarySolution d) t x-
        magneticBoundaryField (datumBoundarySolution d) t x'‖≤D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      ‖retardedElectricDensity {s with E:=E,B:=B} t x (x+z)-
        retardedElectricDensity {s' with E:=E',B:=B'} t x' (x'+z)‖≤C/‖z‖^2 ∧
      ‖retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)-
        retardedMagneticDensity {s' with E:=E',B:=B'} t x' (x'+z)‖≤C/‖z‖^2) :
    ‖s.E (t,x)-s'.E (t,x')‖≤D+C*t ∧ ‖s.B (t,x)-s'.B (t,x')‖≤D+C*t := by
  have he := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell ht x
  have he' := mixed_physical_vector hs'.smooth_f hE' hB' hs'.smooth_E hs'.smooth_B hs'.compact hV'
    hs'.smooth_rho hs'.smooth_current hs'.maxwell ht x'
  have hf1 := (hs.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hg1 := (hs'.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hE1 := (hE.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1 := (hB.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hE1' := (hE'.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1' := (hB'.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hbe := hs.boundary_eq ht x
  have hbe' := hs'.boundary_eq ht x'
  constructor
  · rw [he.1,he'.1,hbe.1,hbe'.1]
    exact norm_boundary_integral_difference ht.le
      (integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
      (integrableOn_retardedElectricDensity_le (s:={s' with E:=E',B:=B'}) hg1 hE1' hB1' hs'.compact ht.le le_rfl x')
      hb.1 (fun z hz hzt => (hden z hz hzt).1)
  · rw [he.2,he'.2,hbe.2,hbe'.2]
    exact norm_boundary_integral_difference ht.le
      (integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
      (integrableOn_retardedMagneticDensity_le (s:={s' with E:=E',B:=B'}) hg1 hE1' hB1' hs'.compact ht.le le_rfl x')
      hb.2 (fun z hz hzt => (hden z hz hzt).2)

lemma uniform_picard_comparison (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (d : Datum) (s s' : Solution) (E B E' B' : Field),
      PicardRegular d s → PicardRegular d s' →
      ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' →
      TransportFor s E B → TransportFor s' E' B' →
      ∀ T : ℝ, T≤1 →
      (∀ r∈Icc 0 T, ∀ x v, |s.f (r,x,v)|≤A ∧ |s'.f (r,x,v)|≤A) →
      (∀ r∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (r,x,v)=0 ∧ s'.f (r,x,v)=0) →
      GlobalFieldBound T L E B → GlobalFieldBound T L E' B' →
      ∀ t∈Ioc 0 T, ∀ x x' : Vec, ∀ D H J : ℝ,
      (‖electricBoundaryField (datumBoundarySolution d) t x-
          electricBoundaryField (datumBoundarySolution d) t x'‖≤D ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t x-
          magneticBoundaryField (datumBoundarySolution d) t x'‖≤D) →
      (∀ r∈Icc 0 T, ∀ z v, |s.f (r,x+z,v)-s'.f (r,x'+z,v)|≤H) →
      (∀ r∈Icc 0 T, ∀ z, ‖E (r,x+z)-E' (r,x'+z)‖≤J ∧
        ‖B (r,x+z)-B' (r,x'+z)‖≤J) →
      ‖s.E (t,x)-s'.E (t,x')‖≤D+C*(max H J)*t ∧
      ‖s.B (t,x)-s'.B (t,x')‖≤D+C*(max H J)*t := by
  obtain ⟨C,hC,hk⟩ := uniform_retarded_density_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro d s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT hab hp hEB hEB' t ht x x' D H J hb hf hdiff
  apply mixed_fields_difference_bound hs hs' hE hB hE' hB' hV hV' ht.1 x x' hb
  intro z hz hzt
  have hr : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  exact hk {s with E:=E,B:=B} {s' with E:=E',B:=B'} T hT hs.smooth_f hs'.smooth_f
    hs.compact hs'.compact hab hp
    (fun r hr y => ⟨(hEB r hr y).1,(hEB r hr y).2,(hEB' r hr y).1,(hEB' r hr y).2⟩)
    t ⟨ht.1.le,ht.2⟩ x x' z hz hzt (max H J)
    (fun v => (hf _ hr z v).trans (le_max_left _ _))
    ((hdiff _ hr z).1.trans (le_max_right _ _)) ((hdiff _ hr z).2.trans (le_max_right _ _))

lemma exists_uniform_limit_geometric {X W : Type*} [NormedAddCommGroup W] [CompleteSpace W]
    {F : ℕ → X → W} {S : Set X} {C : ℝ}
    (h : ∀ n, ∀ x∈S, ‖F (n+1) x-F n x‖≤C*(1/2:ℝ)^n) :
    ∃ f : X → W, TendstoUniformlyOn F f atTop S := by
  let g : ℕ → X → W := fun n x => F (n+1) x-F n x
  have hu : Summable (fun n => C*(1/2:ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).mul_left C
  have hh := tendstoUniformlyOn_tsum_nat hu (f:=g) h
  refine ⟨fun x => F 0 x+∑' n, g n x,?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x hx
  have he : (∑ i∈Finset.range n, g i x)=F n x-F 0 x := Finset.sum_range_sub (fun n => F n x) n
  specialize hn x hx
  rw [he,dist_eq_norm] at hn
  rw [dist_eq_norm]
  convert hn using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  abel

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

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

theorem family_picard_control {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∀ i, FieldControl T L N (fun p : ℝ × Vec => (d i).E₀ p.2) (fun p : ℝ × Vec => (d i).B₀ p.2) ∧
      (∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → FieldControl T L N E B →
        ∀ s : Solution, PicardRegular (d i) s → TransportFor s E B →
          LocalParticleBound T A R P s.f ∧ PhaseParticleLip T M s.f ∧ FieldControl T L N s.E s.B) ∧
      (∀ (E B E' B' : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
        ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' → FieldControl T L N E B → FieldControl T L N E' B' →
        ∀ (s s' : Solution), PicardRegular (d i) s → PicardRegular (d i) s' →
          TransportFor s E B → TransportFor s' E' B' →
        ∀ D : ℝ, 0≤D →
          (∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D ∧ ‖B (t,x)-B' (t,x)‖≤D) →
          ∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)-s'.E (t,x)‖≤D/2 ∧ ‖s.B (t,x)-s'.B (t,x)‖≤D/2) := by
  obtain ⟨T₀,A,R,P,L,hT₀,hT₀1,hA,hR,hP,hL,hfamily⟩ :=
    family_global_picard_invariance hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  obtain ⟨C,hC,hcomp⟩ := uniform_picard_comparison A P L
  let N := D₀+1
  let M := A₁*Real.exp 1
  let K := 1+2*N+L
  have hN : 0<N := by dsimp [N]; linarith
  have hM : 0≤M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  let T := min T₀ (min K⁻¹ (min (C*(M+N)+1)⁻¹ (2*C*(2*M+1)+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hTT : T≤T₀ := min_le_left _ _
  have hT1 : T≤1 := hTT.trans hT₀1
  have hTK : K*T≤1 := by
    have hh : T≤K⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ hK).mp (show T≤1/K by simpa only [one_div] using hh)
    nlinarith
  have hTC : C*(M+N)*T≤1 := by
    have hh : T≤(C*(M+N)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<C*(M+N)+1)).mp
      (show T≤1/(C*(M+N)+1) by simpa only [one_div] using hh)
    nlinarith
  have hTC' : 2*C*(2*M+1)*T≤1 := by
    have hh : T≤(2*C*(2*M+1)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<2*C*(2*M+1)+1)).mp
      (show T≤1/(2*C*(2*M+1)+1) by simpa only [one_div] using hh)
    nlinarith
  have hexp {r : ℝ} (hr : r≤T) : Real.exp (K*r)≤Real.exp 1 :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hr hK.le).trans hTK)
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_⟩
  intro i
  obtain ⟨h₀,hstep⟩ := hfamily i
  have hDinit := (hcaps i).fields_lip
  have hDb := (hcaps i).boundary_lip
  have hAf' := (hcaps i).particle_lip
  have hbase {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular (d i) s) (hV : TransportFor s E B) :=
    hstep T hT.le hTT E B hE hB hc.1 s hs hV
  have hflip {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular (d i) s) (hV : TransportFor s E B) :
      PhaseParticleLip T M s.f := by
    intro t ht z z'
    have hh := transported_spatial_lipschitz hs hE hB hV hA₁ hL.le hN.le hAf'
      (fun r hr x => (hc.1 r hr x).2) (fun r hr x y => (hc.2 r hr x y).1)
      (fun r hr x y => (hc.2 r hr x y).2) ht z z'
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp le_rfl) hA₁) (norm_nonneg _))
  refine ⟨?_,?_,?_⟩
  · constructor
    · exact fun t ht x => h₀ t ⟨ht.1,ht.2.trans hTT⟩ x
    · intro t ht x y
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
  · intro E B hE hB hc s hs hV
    have hp := (hbase hE hB hc hs hV).1
    have hf := hflip hE hB hc hs hV
    refine ⟨hp,hf,(hbase hE hB hc hs hV).2,?_⟩
    intro t ht x y
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_E,hs.initial_B,hs.initial_B]
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
    · have hh := hcomp (d i) s s E B E B hs hs hE hB hE hB hV hV T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp r hr z v).1⟩)
        (by
          intro r hr z v hv
          have hz : s.f (r,z,v)=0 := by
            by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          exact ⟨hz,hz⟩)
        hc.1 hc.1 t ⟨ht0,ht.2⟩ y x (D₀*‖y-x‖) (M*‖y-x‖) (N*‖y-x‖)
        (hDb t ⟨ht0,ht.2.trans hT1⟩ x y)
        (by
          intro r hr z v
          simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
            max_eq_left (norm_nonneg _),add_sub_add_right_eq_sub] using hf r hr (y+z,v) (x+z,v))
        (by
          intro r hr z
          simpa only [add_sub_add_right_eq_sub] using hc.2 r hr (x+z) (y+z))
      have hm : max (M*‖y-x‖) (N*‖y-x‖)≤(M+N)*‖y-x‖ := by
        apply max_le <;> nlinarith [norm_nonneg (y-x)]
      have hb : D₀*‖y-x‖+C*max (M*‖y-x‖) (N*‖y-x‖)*t≤N*‖y-x‖ := by
        calc
          _ ≤ D₀*‖y-x‖+C*((M+N)*‖y-x‖)*T := add_le_add le_rfl
            (mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity))
          _ = (D₀+C*(M+N)*T)*‖y-x‖ := by ring
          _ ≤ N*‖y-x‖ := mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩
  · intro E B E' B' hE hB hE' hB' hc hc' s s' hs hs' hV hV' D hD hdiff t ht x
    have hp := (hbase hE hB hc hs hV).1
    have hp' := (hbase hE' hB' hc' hs' hV').1
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      simp only [hs.initial_E,hs'.initial_E,hs.initial_B,hs'.initial_B,sub_self,norm_zero]
      exact ⟨by positivity,by positivity⟩
    · have hfd (r : ℝ) (hr : r∈Icc 0 T) (z : Phase) : |s.f (r,z)-s'.f (r,z)|≤2*M*D := by
        have hh := transported_comparison hs.smooth_f hs'.smooth_f hE hB hE' hB' hV hV'
          hs.initial_f hs'.initial_f hA₁ hL.le hN.le hD hAf'
          (fun u hu w => (hc.1 u hu w).2) (fun u hu w w' => (hc.2 u hu w w').1)
          (fun u hu w w' => (hc.2 u hu w w').2)
          (fun u hu w => (hdiff u hu w).1) (fun u hu w => (hdiff u hu w).2) hr z z
        simp only [sub_self,norm_zero,zero_add] at hh
        apply hh.trans
        calc
          A₁*(2*D*r)*Real.exp ((1+2*N+L)*r) = (2*D*r)*(A₁*Real.exp (K*r)) := by ring
          _ ≤ (2*D*r)*M := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hexp hr.2) hA₁) (mul_nonneg (mul_nonneg (by norm_num) hD) hr.1)
          _ ≤ (2*D*1)*M := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hr.2.trans hT1) (by positivity)) hM
          _ = 2*M*D := by ring
      have hh := hcomp (d i) s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp' r hr z v).1⟩)
        (by
          intro r hr z v hv
          constructor
          · by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          · by_contra hn
            exact (not_lt_of_ge ((hp' r hr z v).2 hn).2) hv)
        hc.1 hc'.1 t ⟨ht0,ht.2⟩ x x 0 (2*M*D) D (by simp)
        (fun r hr z v => hfd r hr (x+z,v)) (fun r hr z => hdiff r hr (x+z))
      have hm : max (2*M*D) D≤(2*M+1)*D := by apply max_le <;> nlinarith
      have hb : 0+C*max (2*M*D) D*t≤D/2 := by
        calc
          _ ≤ C*((2*M+1)*D)*T := by
            simpa only [zero_add] using mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity)
          _ = (2*C*(2*M+1)*T)*(D/2) := by ring
          _ ≤ 1*(D/2) := mul_le_mul_of_nonneg_right hTC' (by positivity)
          _ = D/2 := one_mul _
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩

theorem family_contractive_picard_sequence {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∀ i, ∃ S : ℕ → Solution, S 0=datumBoundarySolution (d i) ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular (d i) (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        ∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,hfamily⟩ :=
    family_picard_control hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_⟩
  intro i
  obtain ⟨h₀,hstep,hcontract⟩ := hfamily i
  let Q := {s : Solution // ContDiff ℝ ∞ s.E ∧ ContDiff ℝ ∞ s.B}
  have hchoose (q : Q) : ∃ r : Q, PicardRegular (d i) r.1 ∧ TransportFor r.1 q.1.E q.1.B := by
    obtain ⟨s,hs,hV⟩ := exists_picard_regular (hd i) q.2.1 q.2.2
    exact ⟨⟨s,hs.smooth_E,hs.smooth_B⟩,hs,hV⟩
  choose step hs using hchoose
  let q₀ : Q := ⟨datumBoundarySolution (d i),
    (hd i).2.2.2.1.1.comp contDiff_snd,(hd i).2.2.2.2.1.1.comp contDiff_snd⟩
  let q : ℕ → Q := fun n => step^[n] q₀
  have hrec (n : ℕ) : q (n+1)=step (q n) := Function.iterate_succ_apply' step n q₀
  have hbound (n : ℕ) : FieldControl T L N (q n).1.E (q n).1.B := by
    induction n with
    | zero => exact h₀
    | succ n ih =>
      rw [hrec]
      exact (hstep _ _ (q n).2.1 (q n).2.2 ih _ (hs (q n)).1 (hs (q n)).2).2.2
  have hreg (n : ℕ) : PicardRegular (d i) (q (n+1)).1 ∧ TransportFor (q (n+1)).1 (q n).1.E (q n).1.B ∧
      LocalParticleBound T A R P (q (n+1)).1.f ∧ PhaseParticleLip T M (q (n+1)).1.f := by
    rw [hrec]
    exact ⟨(hs (q n)).1,(hs (q n)).2,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).1,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).2.1⟩
  refine ⟨fun n => (q n).1,rfl,
    fun n => (q n).2,hbound,hreg,?_⟩
  intro n
  induction n with
  | zero =>
    intro t ht x
    have h0 := (hbound 0).1 t ht x
    have h1 := (hbound 1).1 t ht x
    simp only [pow_zero,mul_one]
    constructor
    · exact (norm_sub_le _ _).trans (by linarith [h0.1,h1.1])
    · exact (norm_sub_le _ _).trans (by linarith [h0.2,h1.2])
  | succ n ih =>
    have hh := hcontract (q (n+1)).1.E (q (n+1)).1.B (q n).1.E (q n).1.B
      (q (n+1)).2.1 (q (n+1)).2.2 (q n).2.1 (q n).2.2 (hbound (n+1)) (hbound n)
      (q (n+1+1)).1 (q (n+1)).1 (hreg (n+1)).1 (hreg n).1 (hreg (n+1)).2.1 (hreg n).2.1
      (2*L*(1/2:ℝ)^n) (by positivity) ih
    intro t ht x
    convert hh t ht x using 1 <;> rw [pow_succ] <;> ring_nf

theorem family_picard_field_limit_oai {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∀ i, ∃ (S : ℕ → Solution) (E B : Field), S 0=datumBoundarySolution (d i) ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular (d i) (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        (∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) ∧
        TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T} ∧
        TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T} ∧
        ContinuousOn E {p | p.1∈Icc 0 T} ∧ ContinuousOn B {p | p.1∈Icc 0 T} ∧
        FieldControl T L N E B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,hfamily⟩ :=
    family_contractive_picard_sequence hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_⟩
  intro i
  obtain ⟨S,hS0,hsm,hc,hr,hg⟩ := hfamily i
  obtain ⟨E,hE⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).E) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).1)
  obtain ⟨B,hB⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).B) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).2)
  refine ⟨S,E,B,hS0,hsm,hc,hr,hg,hE,hB,
    hE.continuousOn (Frequently.of_forall fun n => (hsm n).1.continuous.continuousOn),
    hB.continuousOn (Frequently.of_forall fun n => (hsm n).2.continuous.continuousOn),?_,?_⟩
  · intro t ht x
    exact ⟨le_of_tendsto (hE.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.1),
      le_of_tendsto (hB.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.2)⟩
  · intro t ht x y
    exact ⟨le_of_tendsto ((hE.tendsto_at (x:=(t,y)) ht).sub (hE.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.1),
      le_of_tendsto ((hB.tendsto_at (x:=(t,y)) ht).sub (hB.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.2)⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RVM.family_picard_field_limit_oai.{u_1} := @OAI.RVM.family_picard_field_limit_oai.{u_1}
