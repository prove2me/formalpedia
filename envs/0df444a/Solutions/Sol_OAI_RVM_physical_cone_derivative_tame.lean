-- Prove2me | solution 1 for OAI.RVM.physical_cone_derivative_tame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:41:37.801096+00:00
-- url     : https://prove2.me/submissions/b30fa5ac-4186-43f8-b582-1071a609a665

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

lemma norm_iteratedFDeriv_integral_le (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
        ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  induction n with
  | zero =>
    intro W _ _ _ F hF x
    simpa only [norm_iteratedFDeriv_zero] using norm_integral_le_integral_norm (fun a => F a x)
  | succ n ih =>
    intro W _ _ _ F hF x
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y => ∫ a, F a y ∂μ) = (fun y => ∫ a, fderiv ℝ (F a) y ∂μ) := by
      funext y
      exact (hasFDerivAt_integral_smoothFamily μ hF y).fderiv
    rw [he]
    simpa only [norm_iteratedFDeriv_fderiv] using ih hF.derivFamily x

end CompactFamily

variable {E W : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

attribute [local instance] Measure.Subtype.measureSpace in
lemma norm_iteratedFDeriv_intervalIntegral_le {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) {a b : ℝ} (hab : a≤b) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ r in a..b, F (r,y)) x‖ ≤
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := norm_iteratedFDeriv_integral_le
    (E:=E) (W:=W) (volume : Measure (Icc a b)) n
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val) x
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  have he' : (∫ r : Icc a b, ‖iteratedFDeriv ℝ n (fun y => F ((r:ℝ),y)) x‖) =
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
    rw [integral_subtype measurableSet_Icc (fun r => ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  simp_rw [he] at hh
  rwa [he'] at hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_TameDerivative
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

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma tame_iteratedFDeriv_comp (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : F → G) (f : E → F), ContDiff ℝ ∞ g  →  ContDiff ℝ ∞ f  →
      ∀ x, (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i g (f x)‖ ≤ A)  →
        (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i f x‖ ≤ A)  →
        ‖iteratedFDeriv ℝ (n+1) (g ∘ f) x‖ ≤
          C*(1+‖iteratedFDeriv ℝ (n+1) g (f x)‖+‖iteratedFDeriv ℝ (n+1) f x‖) := by
  let c : ℕ → ℝ := fun i => (n.choose i : ℝ)*i.factorial*A^(i+1)
  let S := ∑ i∈Finset.range (n+1), c i
  refine ⟨A+S*(A+1),by dsimp [S,c]; positivity,?_⟩
  intro g f hg hf x hgl hfl
  let Mg := ‖iteratedFDeriv ℝ (n+1) g (f x)‖
  let Mf := ‖iteratedFDeriv ℝ (n+1) f x‖
  have hMg : 0 ≤ Mg := norm_nonneg _
  have hMf : 0 ≤ Mf := norm_nonneg _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hcn (i : ℕ) : 0 ≤ c i := by dsimp [c]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hcn i)
  have hfg : fderiv ℝ (g ∘ f) =
      (fun y => ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f y)) (fderiv ℝ f y)) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by simp) (f y)) (hf.differentiable (by simp) y)
  have hcomp (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖ ≤ i.factorial*(A+Mg)*A^i := by
    apply norm_iteratedFDeriv_comp_le (n:=i) (hg.fderiv_right (m:=∞) (by simp)) hf (by exact_mod_cast le_top) x
    · intro j hj
      rw [norm_iteratedFDeriv_fderiv]
      by_cases hjn : j+1 ≤ n
      · exact (hgl (j+1) (by omega) hjn).trans (le_add_of_nonneg_right hMg)
      · have he : j+1=n+1 := by omega
        rw [he]
        exact le_add_of_nonneg_left hA0
    · intro j hj hj'
      exact (hfl j hj (hj'.trans hi)).trans (le_self_pow₀ hA (by omega))
  have hh := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    ((hg.fderiv_right (m:=∞) (by simp)).comp hf) (hf.fderiv_right (m:=∞) (by simp)) x (n:=n) (by exact_mod_cast le_top)
    (ContinuousLinearMap.norm_compL_le ℝ E F G)
  have hterm (i : ℕ) (hi : i∈Finset.range (n+1)) :
      (n.choose i : ℝ)*‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖*
        ‖iteratedFDeriv ℝ (n-i) (fderiv ℝ f) x‖  ≤
      c i*(A+Mg)+(if i=0 then A*Mf else 0) := by
    have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
    rw [norm_iteratedFDeriv_fderiv]
    by_cases hi0 : i=0
    · subst i
      simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,norm_iteratedFDeriv_zero,Function.comp_apply,
        Nat.sub_zero,ite_true]
      have hg1 : ‖fderiv ℝ g (f x)‖ ≤ A := by simpa only [norm_iteratedFDeriv_one] using hgl 1 le_rfl hn
      exact (mul_le_mul_of_nonneg_right hg1 hMf).trans (le_add_of_nonneg_left (mul_nonneg (hcn 0) (add_nonneg hA0 hMg)))
    · rw [ite_eq_right hi0,add_zero]
      have hlow := hfl (n-i+1) (by omega) (by omega)
      calc
        _  ≤  (n.choose i : ℝ)*(i.factorial*(A+Mg)*A^i)*A := by
          gcongr
          exact hcomp i hi'
        _ = c i*(A+Mg) := by dsimp [c]; rw [pow_succ]; ring
  rw [← norm_iteratedFDeriv_fderiv,hfg]
  refine hh.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<n+1 by omega,ite_true]
  change S*(A+Mg)+A*Mf ≤ (A+S*(A+1))*(1+Mg+Mf)
  nlinarith [mul_nonneg hS hMg,mul_nonneg hS hMf,mul_nonneg (mul_nonneg hS hA0) hMg,
    mul_nonneg (mul_nonneg hS hA0) hMf,mul_nonneg hA0 hMg]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {U V W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma norm_iteratedFDeriv_precomp_contraction (f : V → W) (hf : ContDiff ℝ ∞ f)
    (L : U →L[ℝ] V) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  exact ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le _).trans (by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)).trans_eq (mul_one _))

lemma norm_iteratedFDeriv_pair_le {f : U → V} {g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) {C : ℝ}
    (hb : ‖iteratedFDeriv ℝ n f x‖ ≤ C) (hc : ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun z => (f z,g z)) x‖ ≤ C := by
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (by exact_mod_cast le_top)]
  apply ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg _).trans hb)
  intro m
  rw [ContinuousMultilinearMap.prod_apply,Prod.norm_mk]
  exact max_le ((ContinuousMultilinearMap.le_opNorm _ m).trans
    (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
    ((ContinuousMultilinearMap.le_opNorm _ m).trans
    (mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg fun _ _ => norm_nonneg _)))

lemma tame_comp_on_compact {g : V → W} (hg : ContDiff ℝ ∞ g) {K : Set V}
    (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : U → V), ContDiff ℝ ∞ f → ∀ x, f x∈K →
      (∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A) →
      ‖iteratedFDeriv ℝ (n+1) (g ∘ f) x‖ ≤ C*(1+‖iteratedFDeriv ℝ (n+1) f x‖) := by
  have hb (i : Fin (n+2)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hK.image (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))).isBounded.exists_norm_le
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let D : ℝ := A+∑ i, B i
  have hAD : A ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hD : 1 ≤ D := hA.trans hAD
  have hBD (i : Fin (n+2)) : B i ≤ D :=
    (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hA))
  obtain ⟨C,hC,hcomp⟩ := tame_iteratedFDeriv_comp (E:=U) (F:=V) (G:=W) n hn D hD
  refine ⟨C*(1+D),mul_nonneg hC (by linarith),?_⟩
  intro f hf x hx hlow
  have hh := hcomp g f hg hf x
    (fun i hi hi' => (hbound ⟨i,by omega⟩ _ hx).trans (hBD _))
    (fun i hi hi' => (hlow i hi hi').trans hAD)
  have ht := (hbound ⟨n+1,by omega⟩ _ hx).trans (hBD _)
  refine hh.trans (mul_le_mul_of_nonneg_left (by gcongr) hC |>.trans ?_)
  have hd := mul_nonneg (show 0 ≤ D by linarith) (norm_nonneg (iteratedFDeriv ℝ (n+1) f x))
  nlinarith

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleTame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma norm_iteratedFDeriv_phase_slice {f : Phase → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x v : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => f (y,v)) x‖ ≤ ‖iteratedFDeriv ℝ n f (x,v)‖ := by
  let g : Phase → ℝ := fun z => f (z+(0,v))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have hh := norm_iteratedFDeriv_precomp_contraction g hg (ContinuousLinearMap.inl ℝ Vec Vec)
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro w
      simp only [ContinuousLinearMap.inl_apply,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg w),one_mul]
      exact le_rfl) n x
  simpa only [g,Function.comp_def,ContinuousLinearMap.inl_apply,iteratedFDeriv_comp_add_right,
    Prod.mk_add_mk,add_zero,zero_add] using hh

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

lemma uniform_normalised_integrand_tame (k : ℕ) (hk : 1 ≤ k) (P A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 → ∀ v : Vec, ‖v‖ ≤ P →
      ∀ (f : Vec → ℝ) (E B : Vec → Vec), ContDiff ℝ ∞ f → ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ x, (∀ i : ℕ, i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ A ∧
        ‖iteratedFDeriv ℝ i E x‖ ≤ A ∧ ‖iteratedFDeriv ℝ i B x‖ ≤ A) →
      ∀ H : ℝ, 0 ≤ H → ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ H →
        ‖iteratedFDeriv ℝ (k+1) E x‖ ≤ H → ‖iteratedFDeriv ℝ (k+1) B x‖ ≤ H →
      ‖iteratedFDeriv ℝ (k+1) (fun y => normalisedPhysicalIntegrand ((r,n,v),(f y,E y,B y))) x‖ ≤ C*(1+H) := by
  obtain ⟨δ,hδ,hden⟩ := uniform_cone_denominator P
  let K : Set ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) :=
    (Icc (0:ℝ) 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ closedBall 0 A
  have hK : IsCompact K := (isCompact_Icc.prod ((isCompact_sphere _ _).prod
    (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  obtain ⟨C,hC,hcomp⟩ := tame_comp_on_compact (U:=Vec) (smoothNormalisedPhysical_smooth hδ) hK k hk A hA
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv f E B hf hE hB x hlow H hH hft hEt hBt
  let a : Vec → (ℝ × Vec × Vec) × (ℝ × Vec × Vec) := fun y => ((r,n,v),(f y,E y,B y))
  have ha : ContDiff ℝ ∞ a := contDiff_const.prodMk (hf.prodMk (hE.prodMk hB))
  have harg (i : ℕ) (hi : 1 ≤ i) {D : ℝ} (hD : 0 ≤ D)
      (hfD : ‖iteratedFDeriv ℝ i f x‖ ≤ D) (hED : ‖iteratedFDeriv ℝ i E x‖ ≤ D)
      (hBD : ‖iteratedFDeriv ℝ i B x‖ ≤ D) : ‖iteratedFDeriv ℝ i a x‖ ≤ D := by
    apply norm_iteratedFDeriv_pair_le contDiff_const (hf.prodMk (hE.prodMk hB))
    · simpa only [iteratedFDeriv_const_of_ne (by omega : i≠0),Pi.zero_apply,norm_zero] using hD
    · exact norm_iteratedFDeriv_pair_le hf (hE.prodMk hB) i x hfD
        (norm_iteratedFDeriv_pair_le hE hB i x hED hBD)
  have hx : a x∈K := by
    refine ⟨⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
      by simpa only [mem_closedBall_zero_iff] using hv⟩,?_⟩
    rw [mem_closedBall_zero_iff]
    exact max_le (by simpa only [norm_iteratedFDeriv_zero] using (hlow 0 (Nat.zero_le _)).1)
      (max_le (by simpa only [norm_iteratedFDeriv_zero] using (hlow 0 (Nat.zero_le _)).2.1)
        (by simpa only [norm_iteratedFDeriv_zero] using (hlow 0 (Nat.zero_le _)).2.2))
  have hh := hcomp a ha x hx (fun i hi hi' =>
    harg i hi (zero_le_one.trans hA) (hlow i hi').1 (hlow i hi').2.1 (hlow i hi').2.2)
  have he : smoothNormalisedPhysical δ ∘ a =
      (fun y => normalisedPhysicalIntegrand ((r,n,v),(f y,E y,B y))) := by
    funext y
    exact smoothNormalisedPhysical_eq hδ (a y) (hden n v hn hv)
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [harg (k+1) (by omega) hH hft hEt hBt]) hC)

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

lemma compactPolarIntegral_derivative_bound (G : (ℝ × Vec × Vec) × Vec → Vec)
    (hG : ContDiff ℝ ∞ G) (n : ℕ) (H : ℝ → ℝ) (hH : Continuous H)
    (hb : ∀ r∈Icc (0:ℝ) t, ∀ a : Vec, ‖a‖=1 → ∀ v : Vec, ‖v‖≤P →
      ∀ x, ‖iteratedFDeriv ℝ n (fun y => G ((r,a,v),y)) x‖ ≤ H r) (x : Vec) :
    ‖iteratedFDeriv ℝ n (compactPolarIntegral t P G) x‖ ≤
      (4*Real.pi)*volume.real (closedBall (0:Vec) P)*(∫ r in Icc (0:ℝ) t, H r) := by
  have hfamily : SmoothCompactFamily (fun p : ConeParameters t P => fun x =>
      G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),x)) :=
    SmoothCompactFamily.ofJoint hG
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  have hj := norm_iteratedFDeriv_integral_le (coneParameterMeasure t P) n hfamily x
  have hD : Continuous (fun p : ConeParameters t P =>
      ‖iteratedFDeriv ℝ n (fun y => G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),y)) x‖) :=
    ((hfamily.2 n).comp (continuous_const.prodMk continuous_id)).norm
  have hhc : Continuous (fun p : ConeParameters t P => H (p.2.1:ℝ)) :=
    hH.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  refine hj.trans ((integral_mono (hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hhc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun p =>
      hb _ p.2.1.2 _ (sphere_norm p.1) _ (mem_closedBall_zero_iff.mp p.2.2.2) x)).trans_eq ?_)
  unfold coneParameterMeasure
  rw [integral_prod _ (hhc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have he : (∫ p : Icc (0:ℝ) t × closedBall (0:Vec) P, H (p.1:ℝ) ∂volume.prod volume) =
      volume.real (closedBall (0:Vec) P)*(∫ r in Icc (0:ℝ) t, H r) := by
    have hc : Continuous (fun p : Icc (0:ℝ) t × closedBall (0:Vec) P => H (p.1:ℝ)) :=
      hH.comp (continuous_subtype_val.comp continuous_fst)
    try dsimp only at *
    rw [integral_prod _ (μ:=volume) (ν:=volume) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    dsimp only
    simp_rw [integral_const,smul_eq_mul]
    rw [integral_const_mul,integral_subtype measurableSet_Icc H]
    congr 1
    exact congrArg ENNReal.toReal (Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet)
  dsimp only
  simp_rw [he,integral_const,smul_eq_mul,sphere_area]
  ring

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

lemma crossCLM_norm_le (a : Vec) : ‖crossCLM a‖≤‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  exact norm_cross_le a

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

lemma uniform_retarded_extension_tame (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution), ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s.E → ContDiff ℝ ∞ s.B →
      ∀ δ : ℝ, 0<δ → (∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v)) →
      ∀ T : ℝ, T≤1 → ParticleJetBound k T A s.f → SpatialJetBound k T A s.E s.B →
      ∀ H : ℝ → ℝ, (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ r∈Icc (0:ℝ) t, ∀ a : Vec, ‖a‖=1 → ∀ v : Vec, ‖v‖≤P →
      ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => normalisedRetardedExtension δ s t ((r,a,v),y)) x‖ ≤
          C*(1+H (t-r)) := by
  obtain ⟨C,hC,hkernel⟩ := uniform_normalised_integrand_tame k hk P A hA
  refine ⟨C,hC,?_⟩
  intro s hf hE hB δ hδ hden T hT hfj hEBj H hH hft hEBt t ht r hr a ha v hv x
  have htr : t-r∈Icc (0:ℝ) T := ⟨by linarith [hr.2],by linarith [ht.2,hr.1]⟩
  have hfs : ContDiff ℝ ∞ (fun y => s.f (t-r,(y,v))) :=
    hf.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hEs := hE.comp ((contDiff_const (c:=t-r)).prodMk contDiff_id)
  have hBs := hB.comp ((contDiff_const (c:=t-r)).prodMk contDiff_id)
  have he : (fun y => normalisedRetardedExtension δ s t ((r,a,v),y)) =
      (fun y => normalisedPhysicalIntegrand ((r,a,v),(s.f (t-r,(y-r • a,v)),
        s.E (t-r,y-r • a),s.B (t-r,y-r • a)))) := by
    funext y
    exact smoothNormalisedPhysical_eq hδ _ (hden a v ha hv)
  rw [he]
  change ‖iteratedFDeriv ℝ (k+1) (fun y => (fun z => normalisedPhysicalIntegrand
    ((r,a,v),(s.f (t-r,(z,v)),s.E (t-r,z),s.B (t-r,z)))) (y-r • a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f:=fun z => normalisedPhysicalIntegrand
    ((r,a,v),(s.f (t-r,(z,v)),s.E (t-r,z),s.B (t-r,z)))) (k+1) (r • a) x]
  apply hkernel r ⟨hr.1,hr.2.trans (ht.2.trans hT)⟩ a ha v hv _ _ _ hfs hEs hBs (x-r • a)
  · intro i hi
    refine ⟨(norm_iteratedFDeriv_phase_slice (hf.comp (contDiff_const.prodMk contDiff_id)) i _ v).trans
      (hfj _ htr i hi _),(hEBj _ htr _ i hi).1,(hEBj _ htr _ i hi).2⟩
  · exact hH _ htr
  · exact (norm_iteratedFDeriv_phase_slice (hf.comp (contDiff_const.prodMk contDiff_id)) (k+1) _ v).trans
      (hft _ htr _)
  · exact (hEBt _ htr _).1
  · exact (hEBt _ htr _).2

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_Icc_sub (H : ℝ → ℝ) {t : ℝ} (ht : 0≤t) :
    (∫ r in Icc (0:ℝ) t, H (t-r))=∫ r in Icc (0:ℝ) t, H r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht,← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left]
  simp only [sub_self,sub_zero]

lemma physical_cone_derivative_tame_oai (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution), ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s.E → ContDiff ℝ ∞ s.B →
      CompactOnFiniteHorizons s → ∀ T : ℝ, T≤1 →
      (∀ u∈Icc (0:ℝ) T, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) →
      ParticleJetBound k T A s.f → SpatialJetBound k T A s.E s.B →
      ∀ H : ℝ → ℝ, Continuous H → (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
          retardedElectricDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
          retardedMagneticDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) := by
  obtain ⟨K,hK,hkernel⟩ := uniform_retarded_extension_tame k hk P A hA
  obtain ⟨δ,hδ,hden⟩ := uniform_cone_denominator P
  refine ⟨(4*Real.pi)*volume.real (closedBall (0:Vec) P)*K,by positivity,?_⟩
  intro s hf hE hB hc T hT hsupport hfj hEBj H hH hHpos hft hEBt t ht x
  let G := normalisedRetardedExtension δ s t
  have hG : ContDiff ℝ ∞ G := normalisedRetardedExtension_smooth hδ hf hE hB t
  have hsupport' : ∀ u∈Icc (0:ℝ) t, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0 :=
    fun u hu => hsupport u ⟨hu.1,hu.2.trans ht.2⟩
  have hGb : ∀ r∈Icc (0:ℝ) t, ∀ a : Vec, ‖a‖=1 → ∀ v : Vec, ‖v‖≤P →
      ∀ y, ‖iteratedFDeriv ℝ (k+1) (fun w => G ((r,a,v),w)) y‖≤K*(1+H (t-r)) :=
    hkernel s hf hE hB δ hδ hden T hT hfj hEBj H hHpos hft hEBt t ht
  have hHc : Continuous (fun r => K*(1+H (t-r))) :=
    continuous_const.mul (continuous_const.add (hH.comp (continuous_const.sub continuous_id)))
  have hint : (4*Real.pi)*volume.real (closedBall (0:Vec) P)*
      (∫ r in Icc (0:ℝ) t, K*(1+H (t-r))) =
      (4*Real.pi)*volume.real (closedBall (0:Vec) P)*K*(∫ u in Icc (0:ℝ) t, 1+H u) := by
    rw [integral_const_mul,integral_Icc_sub (fun r => 1+H r) ht.1]
    ring
  constructor
  · rw [retardedElectricDensity_polar_compact hf hE hB hc ht.1 hδ hden hsupport']
    exact (compactPolarIntegral_derivative_bound t P G hG (k+1) _ hHc hGb x).trans_eq hint
  · rw [retardedMagneticDensity_polar_compact hf hE hB hc ht.1 hδ hden hsupport']
    have hGB : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => cross p.1.2.1 (G p)) :=
      contDiff_cross.comp (contDiff_fst.snd.fst.prodMk hG)
    apply (compactPolarIntegral_derivative_bound t P _ hGB (k+1) _ hHc ?_ x).trans_eq hint
    intro r hr a ha v hv y
    have hs : ContDiff ℝ ∞ (fun w => G ((r,a,v),w)) := hG.comp (contDiff_const.prodMk contDiff_id)
    have hb := (crossCLM a).norm_iteratedFDeriv_comp_left (x:=y) hs.contDiffAt (by exact_mod_cast le_top : ((k+1:ℕ):ℕ∞ω)≤∞)
    change ‖iteratedFDeriv ℝ (k+1) ((crossCLM a) ∘ (fun w => G ((r,a,v),w))) y‖ ≤ _
    refine hb.trans ((mul_le_mul_of_nonneg_right (crossCLM_norm_le a) (norm_nonneg _)).trans ?_)
    rw [ha,one_mul]
    exact hGb r hr a ha v hv y

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.physical_cone_derivative_tame_oai := @OAI.RVM.physical_cone_derivative_tame_oai
