-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:34.116041+00:00
-- url     : https://prove2.me/submissions/5e019454-75a5-4398-ae04-161ddfbd25fe

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc025
import Theorems.Thm_OAI_TamingCompatibility_separating_probability_atlas_defect
import Theorems.Thm_OAI_TamingCompatibility_separating_probability_local_quadratic

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_BundleTotalSpaceT2
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Filter
open scoped Topology

lemma bundle_totalSpace_t2 {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [T2Space B] [T2Space F] (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle F E] : T2Space (TotalSpace F E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  by_cases hb : p.proj = q.proj
  · let e := trivializationAt F E p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hq : q ∈ e.source := e.mem_source.mpr (hb ▸ mem_baseSet_trivializationAt F E p.proj)
    have he : e p ≠ e q := fun h => hpq (e.injOn hp hq h)
    exact (e.toOpenPartialHomeomorph.continuousAt hp).disjoint
      (disjoint_nhds_nhds.mpr he) (e.toOpenPartialHomeomorph.continuousAt hq)
  · exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hb) (FiberBundle.continuous_proj F E).continuousAt
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ScalarChartLift
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorLiftSupport_subset (p : X) {f : Space → Space}
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    vectorLiftSupport p f ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hf hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorLiftSupport_compact (p : X) {f : Space → Space}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    IsCompact (vectorLiftSupport p f) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hf)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorChartLift_zero_off (p : X) (f : Space → Space)
    {x : X} (hx : x ∉ vectorLiftSupport p f) : vectorChartLift p f x = 0 := by
  unfold vectorChartLift
  split_ifs with hs
  · exact image_eq_zero_of_notMem_tsupport (fun hz => hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩)
  · rfl

lemma vectorChartLift_smooth (p : X) {f : Space → Space}
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    ContMDiff Model Model ∞ (vectorChartLift p f) := by
  intro x
  by_cases hk : x ∈ vectorLiftSupport p f
  · have hsrc := vectorLiftSupport_subset p hf hk
    have he : vectorChartLift p f =ᶠ[𝓝 x] fun y => f (extChartAt Model p y) := by
      filter_upwards [(isOpen_extChartAt_source p).mem_nhds hsrc] with y hy
      simp only [vectorChartLift,ite_eq_left hy]
    have hchart := contMDiffAt_extChartAt' (I := Model) (n := ∞)
      (by simpa only [extChartAt_source] using hsrc)
    exact ((contMDiff_iff_contDiff.mpr hs).contMDiffAt.comp x hchart).congr_of_eventuallyEq he
  · have he : vectorChartLift p f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(vectorLiftSupport_compact p hc hf).isClosed.isOpen_compl.mem_nhds hk] with y hy
      exact vectorChartLift_zero_off p f hy
    exact contMDiffAt_const.congr_of_eventuallyEq he

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RiemannianSmoothLipschitz
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set _root_.MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

lemma smooth_mfderiv_uniform_bound {f : X → Space} (hf : ContMDiff Model Model ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : X) (v : TangentSpace Model x),
      ‖mfderiv Model Model f x v‖ ≤ C*‖v‖ := by
  have hc : Continuous (fun p : TangentBundle Model X =>
      ‖mfderiv Model Model f p.proj p.2‖) :=
    (((contMDiff_snd_tangentBundle_modelSpace (n := ∞) Space Model).continuous.comp
      (hf.continuous_tangentMap (by simp))).norm)
  obtain ⟨C,hC⟩ := (isCompact_bundle_unitSphere (E := TangentSpace Model)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by simp [norm_smul,hnv.ne']
  have hb := hC ⟨x,(‖v‖⁻¹ : ℝ) • v⟩ hu
  simp only [ContinuousLinearMap.map_smul,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_of_pos hnv] at hb
  have hb' := (le_abs_self _).trans hb
  have h : ‖mfderiv Model Model f x v‖ ≤ C*‖v‖ := by
    apply (div_le_iff₀ hnv).mp
    simpa only [div_eq_mul_inv,mul_comm] using hb'
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))

omit [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)] in

lemma smooth_edist_le_length {f : X → Space} (hf : ContMDiff Model Model ∞ f)
    {C : ℝ≥0} (hC : ∀ (x : X) (v : TangentSpace Model x),
      ‖mfderiv Model Model f x v‖ ≤ C*‖v‖)
    {γ : ℝ → X} (hγ : ContMDiff 𝓘(ℝ,ℝ) Model 1 γ) :
    edist (f (γ 1)) (f (γ 0)) ≤ C * pathELength Model γ 0 1 := by
  let η := f ∘ γ
  have hη : ContDiff ℝ 1 η := contMDiff_iff_contDiff.mp ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp hγ)
  calc
    _ = ‖η 1 - η 0‖ₑ := edist_eq_enorm_sub _ _
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη.contDiffOn zero_le_one
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖mfderiv 𝓘(ℝ,ℝ) Model η t 1‖ₑ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp only
      rw [← fderivWithin_derivWithin,
        (hη.differentiable (by simp) t).fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht),
        mfderiv_eq_fderiv]
      rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, (C:ℝ≥0∞)*‖mfderiv 𝓘(ℝ,ℝ) Model γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t _ht
      have he := mfderiv_comp t (hf.mdifferentiable (by simp) (γ t))
        (hγ.mdifferentiable (by simp) t)
      change ‖mfderiv 𝓘(ℝ,ℝ) Model (f ∘ γ) t 1‖ₑ ≤ _
      rw [he,ContinuousLinearMap.comp_apply]
      have h := ENNReal.ofReal_le_ofReal (hC (γ t) (mfderiv 𝓘(ℝ,ℝ) Model γ t 1))
      simpa only [← ofReal_norm,ENNReal.ofReal_mul C.coe_nonneg,ENNReal.ofReal_coe_nnreal] using h
    _ = C * pathELength Model γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,pathELength]

theorem smooth_lipschitz_riemannian {f : X → Space} (hf : ContMDiff Model Model ∞ f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y : X,
      edist (f x) (f y) ≤ C * riemannianEDist Model x y := by
  obtain ⟨C,hCp,hC⟩ := smooth_mfderiv_uniform_bound hf
  lift C to ℝ≥0 using hCp.le
  refine ⟨C,hCp,?_⟩
  intro x y
  have hCnp : (C:ℝ≥0∞) ≠ 0 := by exact_mod_cast hCp.ne'
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hεfin
  by_cases hd : riemannianEDist Model x y = ⊤
  · simp [hd,hCnp]
  have hd' : riemannianEDist Model x y < riemannianEDist Model x y + ε/(C:ℝ≥0∞) := by
    exact ENNReal.lt_add_right hd (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hε.ne', ENNReal.coe_ne_top⟩)
  obtain ⟨γ,hγx,hγy,hγ,hγlen,_⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hd' zero_lt_one
  have hh := smooth_edist_le_length hf hC hγ
  rw [hγx,hγy,edist_comm] at hh
  calc
    _ ≤ C * pathELength Model γ 0 1 := hh
    _ ≤ C * (riemannianEDist Model x y + ε/(C:ℝ≥0∞)) := by gcongr
    _ = C*riemannianEDist Model x y + ε := by
      rw [mul_add,ENNReal.mul_div_cancel (by exact_mod_cast hCp.ne') ENNReal.coe_ne_top]
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RiemannianChartControl
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms Set Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem compact_chart_distance_control (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ≥0, 0 < L ∧ ∀ x y : X,
      x ∈ (extChartAt Model p).source → y ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → extChartAt Model p y ∈ K →
      edist (extChartAt Model p x) (extChartAt Model p y) ≤
        L * Manifold.riemannianEDist Model x y := by
  obtain ⟨φ,hφ,hφT,hφone⟩ := SchwartzCutoff.exists_one_on_compact hK
    (isOpen_extChartAt_target p) hKT
  let f : Space → Space := fun z => φ z • z
  have hfs : ContDiff ℝ ∞ f := (φ.smooth ⊤).smul contDiff_id
  have hfc : HasCompactSupport f := hφ.smul_right
  have hfT : tsupport f ⊆ (extChartAt Model p).target :=
    (tsupport_smul_subset_left φ id).trans hφT
  obtain ⟨L,hL,hbound⟩ := smooth_lipschitz_riemannian
    (vectorChartLift_smooth p hfs hfc hfT)
  refine ⟨L,hL,?_⟩
  intro x y hxs hys hxK hyK
  have he (z : X) (hzs : z ∈ (extChartAt Model p).source)
      (hzK : extChartAt Model p z ∈ K) :
      vectorChartLift p f z = extChartAt Model p z := by
    simp only [vectorChartLift,ite_eq_left hzs,f,hφone _ hzK,one_smul]
  simpa only [he x hxs hxK,he y hys hyK] using hbound x y
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TwoDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma two_direction_inner_sq_le (z u v : E) (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    ⟪z,u⟫^2 + ⟪z,v⟫^2 ≤ ‖z‖^2*‖u‖^2 := by
  by_cases hu : u = 0
  · have hv0 : v = 0 := norm_eq_zero.mp (by simpa [hu] using hv)
    simp [hu,hv0]
  have hu2 : 0 < ‖u‖^2 := pow_pos (norm_pos_iff.mpr hu) 2
  have hvu : ⟪v,u⟫ = 0 := by rw [real_inner_comm,huv]
  have hzu : ⟪u,z⟫ = ⟪z,u⟫ := real_inner_comm _ _
  have hzv : ⟪v,z⟫ = ⟪z,v⟫ := real_inner_comm _ _
  have h : 0 ≤ ⟪‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v,
    ‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v⟫ := real_inner_self_nonneg
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    huv,hvu,hzu,hzv] at h
  simp only [real_inner_self_eq_norm_sq,hv] at h
  nlinarith
end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_GeometricSeparatingProbability
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

local instance unitT2 [T2Space X] (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : T2Space (MetricUnit g) := by
  let : T2Space (TangentBundle Model X) := bundle_totalSpace_t2 (TangentSpace Model : X → Type)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_HermitianRadialProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hermitianGraph_complex_pair (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v) (v : E) :
    ⟪hermitianGraph K v, hermitianGraph K (K v)⟫ = 0 ∧
      ‖hermitianGraph K (K v)‖ = ‖hermitianGraph K v‖ := by
  constructor
  · rw [hermitianGraph_inner,hK,inner_neg_right,real_inner_comm]
    ring
  · have he : ‖hermitianGraph K (K v)‖^2 = ‖hermitianGraph K v‖^2 := by
      rw [hermitianGraph_norm_sq,hermitianGraph_norm_sq,hK,norm_neg]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_HermitianDerivativeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hermitianGraph_norm_ge (K : E →L[ℝ] E) (z : E) : ‖z‖ ≤ ‖hermitianGraph K z‖ := by
  have h := hermitianGraph_norm_sq K z
  nlinarith [sq_nonneg ‖K z‖,norm_nonneg (hermitianGraph K z),norm_nonneg z]

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactUniformBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Topology

theorem IsCompact.exists_uniform_monotone_bound {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) (P : Y → ℝ → Prop)
    (hmono : ∀ y a b, a ≤ b → P y a → P y b)
    (hlocal : ∀ q ∈ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 q, P y C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, P y C := by
  classical
  have hloc : ∀ q : K, ∃ C : ℝ, ∃ U : Set Y,
      0 ≤ C ∧ IsOpen U ∧ q.val ∈ U ∧ ∀ y ∈ U, P y C := by
    intro q
    obtain ⟨C,hC,hq⟩ := hlocal q.val q.property
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp hq
    exact ⟨C,U,hC,hU,hqU,hUP⟩
  choose C U hC hU hqU hUP using hloc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hqU ⟨y,hy⟩⟩)
  refine ⟨∑ q ∈ s, C q, Finset.sum_nonneg (fun q _ => hC q), ?_⟩
  intro y hy
  obtain ⟨q,hq,hyq⟩ := mem_iUnion₂.mp (hs hy)
  exact hmono y (C q) _ (Finset.single_le_sum (fun r _ => hC r) hq) (hUP q y hyq)

end


end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_GeometricLocalMass
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set _root_.MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem local_chart_mass_to_riemannian {Y : Type*} [MeasurableSpace Y]
    (proj : Y → X) (μ : Measure Y) [IsProbabilityMeasure μ]
    (hloc : ∀ x : X, ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : Y | proj u ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^2 := by
  let : EMetricSpace X := .ofRiemannianMetric Model X
  let P := fun (x : X) (C : ℝ) => ∀ s : ℝ, 0 < s →
    μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^2
  suffices hlocal : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C by
    obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound (isCompact_univ : IsCompact (univ : Set X))
      P (fun _ a b hab ha s hs => (ha s hs).trans
        (mul_le_mul_of_nonneg_right hab (sq_nonneg s))) hlocal
    exact ⟨C,hC,fun x => hbound x (mem_univ x)⟩
  intro x _hx
  obtain ⟨p,R,C,r,hxs,hR,hC,hr,h4,hmass⟩ := hloc x
  let e := extChartAt Model p
  have h2 : Metric.closedBall (e x) (2*R) ⊆ e.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans h4
  have h1 : Metric.closedBall (e x) R ⊆ e.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans h4
  let K := e.symm '' Metric.closedBall (e x) R
  let W := e.source ∩ e ⁻¹' Metric.ball (e x) (2*R)
  let V := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have hK : IsCompact K := inverse_chart_compact_image p (isCompact_closedBall _ _) h1
  have hW : IsOpen W := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hV : IsOpen V := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxs,by simpa using hR⟩
  have hKW : K ⊆ W := by
    rintro y ⟨z,hz,rfl⟩
    have hzt := h1 hz
    refine ⟨e.map_target hzt,?_⟩
    change dist (e (e.symm z)) (e x) < 2*R
    rw [e.right_inv hzt]
    exact lt_of_le_of_lt hz (by linarith)
  obtain ⟨δ,hδ,hδW⟩ := hK.exists_thickening_subset_open hW hKW
  obtain ⟨L,hL,hbound⟩ := compact_chart_distance_control p (isCompact_closedBall (e x) (2*R)) h2
  let q : ℝ := min δ (r/L)
  have hLp : (0:ℝ) < L := hL
  have hq : 0 < q := lt_min hδ (div_pos hr hLp)
  have hCL : 0 ≤ C*(L:ℝ)^2 := mul_nonneg hC (sq_nonneg _)
  let D : ℝ := C*(L:ℝ)^2 + 1/q^2
  have hD : 0 ≤ D := add_nonneg hCL (by positivity)
  refine ⟨D,hD,?_⟩
  filter_upwards [hV.mem_nhds hxV] with y hy
  intro s hs
  by_cases hsq : s ≤ q
  · have hsδ : s ≤ δ := hsq.trans (min_le_left _ _)
    have hsLr : (L:ℝ)*s ≤ r := by
      have ht := (le_div_iff₀ hLp).mp (hsq.trans (min_le_right _ _))
      simpa only [mul_comm] using ht
    have hyK : y ∈ K := ⟨e y,Metric.ball_subset_closedBall hy.2,e.left_inv hy.1⟩
    have hy2 : e y ∈ Metric.closedBall (e x) (2*R) :=
      (Metric.closedBall_subset_closedBall (by linarith)) (Metric.ball_subset_closedBall hy.2)
    have hsub : {u : Y | riemannianEDist Model y (proj u) < ENNReal.ofReal s} ⊆
        {u : Y | proj u ∈ e.symm '' Metric.closedBall (e y) ((L:ℝ)*s)} := by
      intro u hu
      have huδ : edist (proj u) y < ENNReal.ofReal δ := by
        rw [edist_comm]
        exact hu.trans_le (ENNReal.ofReal_le_ofReal hsδ)
      have huW : proj u ∈ W := hδW ((Metric.mem_thickening_iff_exists_edist_lt K (proj u)).mpr ⟨y,hyK,huδ⟩)
      have hc := hbound y (proj u) hy.1 huW.1 hy2 (Metric.ball_subset_closedBall huW.2)
      have hcoord : dist (e (proj u)) (e y) ≤ (L:ℝ)*s := by
        apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg L.coe_nonneg hs.le)).mp
        rw [ENNReal.ofReal_mul L.coe_nonneg,ENNReal.ofReal_coe_nnreal,← edist_dist,edist_comm]
        exact hc.trans (by gcongr; exact hu.le)
      exact ⟨e (proj u),hcoord,e.left_inv huW.1⟩
    calc
      _ ≤ μ.real {u : Y | proj u ∈ e.symm '' Metric.closedBall (e y) ((L:ℝ)*s)} := measureReal_mono hsub
      _ ≤ C*((L:ℝ)*s)^2 := hmass _ ⟨mul_pos hLp hs,hsLr⟩ _ (Metric.ball_subset_closedBall hy.2)
      _ = (C*(L:ℝ)^2)*s^2 := by ring
      _ ≤ D*s^2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg s)
  · have hqs : q ≤ s := le_of_lt (lt_of_not_ge hsq)
    have hpow : q^2 ≤ s^2 := pow_le_pow_left₀ hq.le hqs 2
    have hlarge : 1 ≤ (1/q^2)*s^2 := by
      rw [one_div,inv_mul_eq_div]
      exact (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using hpow)
    exact measureReal_le_one.trans (hlarge.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) (sq_nonneg s)))
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianDefect_nonneg (K : E →L[ℝ] E)
    (hK : ∀ v, K (K v) = -v) (z v : E) : 0 ≤ hermitianDefect K z v := by
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := two_direction_inner_sq_le (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  dsimp only [hermitianDefect]
  linarith

end TamingCompatibility.RadialPotential

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialUnitCoordinates
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

omit [CompactSpace X] [T2Space X] in
lemma unitRadialDefect_nonneg (p : X) {b : Space} (hb : b ∈ (extChartAt Model p).target)
    (u : MetricUnit (hermitianMetric J α hs ht)) : 0 ≤ unitRadialDefect J α hs ht p b u :=
  hermitianDefect_nonneg _ (coordinateJ_square J p hb) _ _

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PlaneNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma first_reconstruct (a : V) : ‖a‖ • first a = a := by
  by_cases ha : a = 0
  · simp [ha,first]
  · rw [first,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),one_smul]

lemma second_reconstruct (a b : V) : ‖normalPart a b‖ • second a b = normalPart a b :=
  first_reconstruct _

lemma reconstruct_second (a b : V) :
    b = ⟪first a,b⟫ • first a + ‖normalPart a b‖ • second a b := by
  rw [second_reconstruct,normalPart]
  abel

lemma second_continuousAt {a b : V} (ha : a ≠ 0) (hab : normalPart a b ≠ 0) :
    ContinuousAt (fun p : V × V => second p.1 p.2) (a,b) := by
  change ContinuousAt (first ∘ fun p : V × V => normalPart p.1 p.2) (a,b)
  exact ContinuousAt.comp (x := (a,b))
    (g := first) (f := fun p : V × V => normalPart p.1 p.2)
    (first_continuousAt hab) (normalPart_continuousAt (b := b) ha)

end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShell
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma exists_dyadic_majorant {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    ∃ n : ℕ, d < 2^(n+1)*r ∧ (1+d/r)⁻¹^6 ≤ (1/64:ℝ)^n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near (le_max_left 1 (d/r)) (by norm_num : (1:ℝ)<2)
  have hbase : (2:ℝ)^n ≤ 1+d/r := hn.trans (max_le (le_add_of_nonneg_right (div_nonneg hd hr.le)) (by linarith))
  refine ⟨n,(div_lt_iff₀ hr).mp ((le_max_right 1 (d/r)).trans_lt hn'),?_⟩
  calc
    (1+d/r)⁻¹^6 ≤ ((2:ℝ)^n)⁻¹^6 := by
      gcongr
    _ = (1/64:ℝ)^n := by
      rw [← inv_pow,← pow_mul,Nat.mul_comm,pow_mul,inv_pow]
      norm_num

lemma profile_ofReal {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    profile r (ENNReal.ofReal d) = ENNReal.ofReal ((1+d/r)⁻¹^6) := by
  simp only [profile, ← ENNReal.ofReal_div_of_pos hr, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (div_nonneg hd hr.le)]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow (by positivity)]

lemma profile_top {r : ℝ} : profile r ⊤ = 0 := by
  simp [profile, ENNReal.top_div]

lemma profile_majorant {r : ℝ} (hr : 0 < r) (d : ℝ≥0∞) :
    profile r d ≤ ∑' n : ℕ,
      {e : ℝ≥0∞ | e < ENNReal.ofReal (2^(n+1)*r)}.indicator
        (fun _ => ENNReal.ofReal ((1/64:ℝ)^n)) d := by
  by_cases hd : d = ⊤
  · rw [hd,profile_top]; exact bot_le
  obtain ⟨n,hn,hbound⟩ := exists_dyadic_majorant hr d.toReal_nonneg
  have hdreal : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hd
  have hn' : d < ENNReal.ofReal (2^(n+1)*r) := by
    rw [←hdreal]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hn
  calc
    _ = ENNReal.ofReal ((1+d.toReal/r)⁻¹^6) := by rw [←hdreal,profile_ofReal hr d.toReal_nonneg]; simp [hdreal]
    _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by simp only [indicator, mem_ofPred_eq, hn', ↓reduceIte]
    _ ≤ _ := ENNReal.le_tsum n

lemma dyadic_term_identity (C r : ℝ) (n : ℕ) :
    (1/64:ℝ)^n*(C*(2^(n+1)*r)^2) = 4*C*r^2*(1/16:ℝ)^n := by
  have hpow : ((2:ℝ)^n)^2 = ((2:ℝ)^2)^n := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ = 4*C*r^2*((1/64:ℝ)^n*((2:ℝ)^2)^n) := by rw [pow_succ,←hpow]; ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem lintegral_profile_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ENNReal.ofReal (8*C*r^2) := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  have hi (n : ℕ) : ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := by
    rw [lintegral_indicator_const (measurableSet_lt hδ measurable_const)]
    have hm : μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} ≤
        ENNReal.ofReal (C*(2^(n+1)*r)^2) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hgrowth _ (by positivity))
    calc
      _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) * ENNReal.ofReal (C*(2^(n+1)*r)^2) :=
        by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), dyadic_term_identity]
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := ENNReal.tsum_le_tsum hi
    _ = ENNReal.ofReal (4*C*r^2) * (1-ENNReal.ofReal (1/16))⁻¹ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4*C*r^2), ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/16)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (8*C*r^2) := by
      have hratio : (1-ENNReal.ofReal (1/16))⁻¹ ≤ ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/16)]
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1-1/16)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      calc
        _ ≤ ENNReal.ofReal (4*C*r^2)*ENNReal.ofReal 2 := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end QuadraticShell

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthMomentKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Bundle Set TopologicalSpace
lemma bundle_totalSpace_secondCountable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [SecondCountableTopology B] [SecondCountableTopology F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] :
    SecondCountableTopology (TotalSpace F E) := by
  let e : B → Trivialization F (π F E) := fun b => trivializationAt F E b
  obtain ⟨s,hsc,hs⟩ := isOpen_iUnion_countable (fun b => (e b).baseSet) (fun b => (e b).open_baseSet)
  have hcover : (⋃ b : B, (e b).baseSet) = univ := by
    apply eq_univ_iff_forall.mpr
    intro b
    exact mem_iUnion.mpr ⟨b,mem_baseSet_trivializationAt F E b⟩
  rw [hcover] at hs
  let := hsc.to_subtype
  let U : s → Set (TotalSpace F E) := fun b => (e b.val).source
  have (b : s) : SecondCountableTopology (U b) :=
    (e b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U) (fun b => (e b.val).open_source)
  apply eq_univ_iff_forall.mpr
  intro v
  have hv : v.proj ∈ ⋃ b ∈ s, (e b).baseSet := hs.symm ▸ mem_univ _
  obtain ⟨b,hb,hv⟩ := mem_iUnion₂.mp hv
  exact mem_iUnion.mpr ⟨⟨b,hb⟩,(e b).mem_source.mpr hv⟩
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [SecondCountableTopology X]
lemma unitSecondCountable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    SecondCountableTopology (MetricUnit g) := by
  have : SecondCountableTopology (TangentBundle Model X) :=
    bundle_totalSpace_secondCountable (TangentSpace Model : X → Type)
  exact TopologicalSpace.Subtype.secondCountableTopology {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1}
end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration

lemma radialCoefficient_nonneg (r t : ℝ) : 0 ≤ radialCoefficient r t := by
  unfold radialCoefficient
  positivity

lemma rational_cutoff_bound (r t : ℝ) : radialCoefficient r t*t^4 ≤ 1 := by
  unfold radialCoefficient
  by_cases hz : r^2+t^2 = 0
  · simp [hz]
  have hh : (r*t)^2 ≤ (r^2+t^2)^2 := by nlinarith [sq_nonneg (r-t),sq_nonneg (r+t)]
  have h4 : r^4*t^4 ≤ (r^2+t^2)^4 := by nlinarith [sq_nonneg ((r^2+t^2)^2-(r*t)^2)]
  rw [div_mul_eq_mul_div]
  exact (div_le_one (pow_pos (lt_of_le_of_ne (by positivity) (Ne.symm hz)) 4)).mpr h4

lemma radialCoefficient_mul_defect_bound {r t d : ℝ} (hd : 0 ≤ d) (hz : t = 0 → d = 0) :
    radialCoefficient r t*d ≤ d/t^4 := by
  by_cases ht : t = 0
  · simp [hz ht]
  have ht4 : 0 < t^4 := lt_of_le_of_ne (by positivity) (Ne.symm (pow_ne_zero 4 ht))
  apply (le_div_iff₀ ht4).mpr
  have hh := mul_le_mul_of_nonneg_right (rational_cutoff_bound r t) hd
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma rational_defect_tendsto_zero (D t : Ω → ℝ) (hD : Measurable D) (ht : Measurable t)
    (hDp : ∀ x, 0 ≤ D x) (hzero : ∀ x, t x = 0 → D x = 0)
    (hint : Integrable (fun x => D x/(t x)^4) μ) :
    Tendsto (fun r : ℝ => ∫ x, radialCoefficient r (t x)*D x ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hm (r : ℝ) : Measurable (fun x => radialCoefficient r (t x)*D x) :=
    (measurable_const.div ((measurable_const.add (ht.pow_const 2)).pow_const 4)).mul hD
  have hb (r : ℝ) (x : Ω) : ‖radialCoefficient r (t x)*D x‖ ≤ D x/(t x)^4 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (radialCoefficient_nonneg _ _) (hDp x))]
    exact radialCoefficient_mul_defect_bound (hDp x) (hzero x)
  have hl (x : Ω) : Tendsto (fun r : ℝ => radialCoefficient r (t x)*D x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    by_cases hx : t x = 0
    · simp only [hzero x hx,mul_zero]
      exact tendsto_const_nhds
    · have h4 : Tendsto (fun r : ℝ => r^4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.pow 4) :
          Tendsto (fun r : ℝ => r^4) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)^4)))
      have h2 : Tendsto (fun r : ℝ => r^2+(t x)^2) (𝓝[>] (0:ℝ)) (𝓝 ((t x)^2)) := by
        simpa using ((tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.pow 2)).add
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (t x)^2) (𝓝[>] (0:ℝ)) (𝓝 ((t x)^2))) :
          Tendsto (fun r : ℝ => r^2+(t x)^2) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)^2+(t x)^2)))
      have hh := (h4.div (h2.pow 4) (pow_ne_zero 4 (pow_ne_zero 2 hx))).mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => D x) (𝓝[>] (0:ℝ)) (𝓝 (D x)))
      simpa only [radialCoefficient,Pi.div_apply,zero_div,zero_mul] using hh
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun x => D x/(t x)^4) (Eventually.of_forall (fun r => (hm r).aestronglyMeasurable))
    (Eventually.of_forall (fun r => Eventually.of_forall (hb r))) hint (Eventually.of_forall hl)

end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RationalKernelCompare
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_transverse_sq (u v z : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖transverse u v z‖^2 = ‖z‖^2-⟪u,z⟫^2-⟪v,z⟫^2 := by
  have hvu : ⟪v,u⟫ = 0 := (real_inner_comm _ _).trans huv
  rw [← real_inner_self_eq_norm_sq]
  simp only [transverse,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu,hv,huv,hvu,
    real_inner_comm z u,real_inner_comm z v,one_pow]
  ring

end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneTransverseGraph
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
open RadialPotential
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma transverse_sub (u v z w : V) :
    transverse u v (z-w) = transverse u v z - transverse u v w := by
  simp only [transverse,inner_sub_right,sub_smul]
  abel

lemma transverse_smul (u v z : V) (c : ℝ) :
    transverse u v (c • z) = c • transverse u v z := by
  simp only [transverse,real_inner_smul_right,smul_sub,smul_smul]

lemma norm_transverse_le (u v z : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖transverse u v z‖ ≤ ‖z‖ := by
  have hh := norm_transverse_sq u v z hu hv huv
  nlinarith [sq_nonneg ⟪u,z⟫,sq_nonneg ⟪v,z⟫,norm_nonneg (transverse u v z),norm_nonneg z]

lemma transverse_first (a b : V) (ha : a ≠ 0) (_hab : normalPart a b ≠ 0) :
    transverse (first a) (second a b) a = 0 := by
  have h1 := first_second_orthogonal ha b
  have hv : ⟪second a b,first a⟫ = 0 := (real_inner_comm _ _).trans h1
  conv_lhs => arg 3; rw [← first_reconstruct a]
  rw [transverse_smul]
  simp only [transverse,real_inner_self_eq_norm_sq,norm_first ha,one_pow,one_smul,hv,zero_smul,sub_self,smul_zero]

lemma transverse_second (a b : V) (ha : a ≠ 0) (hab : normalPart a b ≠ 0) :
    transverse (first a) (second a b) b = 0 := by
  have hu := norm_first ha
  have hv := norm_second hab
  have h1 := first_second_orthogonal ha b
  have h2 : ⟪second a b,first a⟫ = 0 := (real_inner_comm _ _).trans h1
  have he (c d : ℝ) : transverse (first a) (second a b) (c • first a + d • second a b) = 0 := by
    simp only [transverse,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      hu,hv,h1,h2,one_pow,mul_one,mul_zero,add_zero,zero_add,add_sub_cancel_left,sub_self]
  conv_lhs => arg 3; rw [reconstruct_second a b]
  exact he _ _

lemma graph_projection_norm (K : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (z a : V) (ha : a ≠ 0) :
    let G := hermitianGraph K
    let c := ⟪G z,G a⟫/‖G a‖^2
    let d := ⟪G z,G (K a)⟫/‖G a‖^2
    ‖G (z-c • a-d • K a)‖ ≤ Real.sqrt (hermitianDefect K z a)/‖G a‖ := by
  dsimp only
  let G := hermitianGraph K
  have han : 0 < ‖G a‖ := lt_of_lt_of_le (norm_pos_iff.mpr ha) (hermitianGraph_norm_ge K a)
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK a
  have hr : ‖G (z-(⟪G z,G a⟫/‖G a‖^2) • a-(⟪G z,G (K a)⟫/‖G a‖^2) • K a)‖^2 =
      hermitianDefect K z a/‖G a‖^2 := by
    simp only [map_sub,map_smul]
    rw [norm_sub_sq_real,norm_sub_sq_real,inner_sub_left]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left,real_inner_smul_right]
    rw [show ⟪G a,G (K a)⟫ = 0 from ho,show ‖G (K a)‖ = ‖G a‖ from hn]
    change _ = (‖G z‖^2*‖G a‖^2-⟪G z,G a⟫^2-⟪G z,G (K a)⟫^2)/‖G a‖^2
    field_simp
    ring
  have hs := Real.sq_sqrt (hermitianDefect_nonneg K hK z a)
  have he : (Real.sqrt (hermitianDefect K z a)/‖G a‖)^2 = hermitianDefect K z a/‖G a‖^2 := by
    rw [div_pow,hs]
  have hp : 0 ≤ Real.sqrt (hermitianDefect K z a)/‖G a‖ := by positivity
  nlinarith [norm_nonneg (G (z-(⟪G z,G a⟫/‖G a‖^2) • a-(⟪G z,G (K a)⟫/‖G a‖^2) • K a))]

lemma graph_coefficient_bound (K : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (z a : V) (ha : a ≠ 0) :
    |⟪hermitianGraph K z,hermitianGraph K (K a)⟫/‖hermitianGraph K a‖^2| * ‖a‖ ≤
      ‖hermitianGraph K z‖ := by
  let G := hermitianGraph K
  have han : 0 < ‖G a‖ := lt_of_lt_of_le (norm_pos_iff.mpr ha) (hermitianGraph_norm_ge K a)
  have hh := abs_real_inner_le_norm (G z) (G (K a))
  rw [(hermitianGraph_complex_pair K hK a).2] at hh
  rw [abs_div, abs_of_nonneg (sq_nonneg ‖hermitianGraph K a‖)]
  have hc : |⟪G z,G (K a)⟫|/‖G a‖^2 ≤ ‖G z‖/‖G a‖ := by
    apply (div_le_div_iff₀ (sq_pos_of_pos han) han).mpr
    nlinarith
  calc
    _ ≤ (‖G z‖/‖G a‖)*‖a‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg a)
    _ ≤ (‖G z‖/‖G a‖)*‖G a‖ := mul_le_mul_of_nonneg_left (hermitianGraph_norm_ge K a) (by positivity)
    _ = _ := div_mul_cancel₀ _ han.ne'

lemma transverse_graph_bound (K L : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (hL : ∀ v, L (L v) = -v) (z a : V) (ha : a ≠ 0) :
    ‖transverse (first a) (second a (L a)) z‖ ≤
      Real.sqrt (hermitianDefect K z a)/‖hermitianGraph K a‖ +
        ‖hermitianGraph K z‖*‖K-L‖ := by
  let G := hermitianGraph K
  let c := ⟪G z,G a⟫/‖G a‖^2
  let d := ⟪G z,G (K a)⟫/‖G a‖^2
  let R := z-c • a-d • K a
  let u := first a
  let v := second a (L a)
  have hab := normalPart_complex_ne_zero L hL ha
  have hu : ‖u‖ = 1 := norm_first ha
  have hv : ‖v‖ = 1 := norm_second hab
  have huv : ⟪u,v⟫ = 0 := first_second_orthogonal ha _
  have hta : transverse u v a = 0 := transverse_first a (L a) ha hab
  have htb : transverse u v (L a) = 0 := transverse_second a (L a) ha hab
  have hz : transverse u v z = transverse u v R + d • transverse u v ((K-L) a) := by
    simp only [R,transverse_sub,transverse_smul,sub_apply,
      hta,htb,sub_zero,smul_zero]
    abel
  calc
    _ ≤ ‖transverse u v R‖+‖d • transverse u v ((K-L) a)‖ := by rw [hz]; exact norm_add_le _ _
    _ ≤ ‖R‖+|d| * ‖(K-L) a‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (norm_transverse_le u v R hu hv huv)
        (mul_le_mul_of_nonneg_left (norm_transverse_le u v _ hu hv huv) (abs_nonneg d))
    _ ≤ ‖G R‖+|d| * (‖K-L‖*‖a‖) := add_le_add (hermitianGraph_norm_ge K R)
      (mul_le_mul_of_nonneg_left ((K-L).le_opNorm a) (abs_nonneg d))
    _ ≤ _ := by
      have hh := graph_projection_norm K hK z a ha
      have hc := mul_le_mul_of_nonneg_right (graph_coefficient_bound K hK z a ha) (norm_nonneg (K-L))
      change ‖G R‖ ≤ _ at hh
      change (|d| * ‖a‖)*‖K-L‖ ≤ _ at hc
      nlinarith
end TamingCompatibility.PlaneVariation

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] [T2Space X] in
lemma unitChartFirst_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartFirst J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  exact (first_continuousAt (unitChartVector_ne_zero J α hs ht p u
    (unitChart_mem J α hs ht p hKT hu).1)).comp_continuousWithinAt
      ((unitChartVector_continuousOn J α hs ht p hKT) u hu)

omit [CompactSpace X] [T2Space X] in
lemma unitChartSecond_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartSecond J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  have ha := unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1
  have hab := normalPart_complex_ne_zero _ (coordinateJ_square J p
    (hKT (unitChart_mem J α hs ht p hKT hu).2)) ha
  apply ContinuousAt.comp_continuousWithinAt
    (f := fun v => (unitChartVector J α hs ht p v,unitChartJVector J α hs ht p v))
    (second_continuousAt ha hab)
  exact     (((unitChartVector_continuousOn J α hs ht p hKT) u hu).prodMk
      ((unitChartJVector_continuousOn J α hs ht p hKT) u hu))

omit [CompactSpace X] [T2Space X] in
lemma unitTransverse_continuousOn (p : X) (b : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitTransverse J α hs ht p b) (unitChartDomain J α hs ht p K) := by
  let f := unitChartFirst J α hs ht p
  let g := unitChartSecond J α hs ht p
  let z := fun u => unitChartBase J α hs ht p u-b
  let S := unitChartDomain J α hs ht p K
  have hc : ContinuousOn z S := (unitChartBase_continuousOn J α hs ht p hKT).sub continuousOn_const
  have hf : ContinuousOn f S := unitChartFirst_continuousOn J α hs ht p hKT
  have hg : ContinuousOn g S := unitChartSecond_continuousOn J α hs ht p hKT
  have hi : ContinuousOn (fun u => inner ℝ (f u) (z u)) S := hf.inner hc
  have hj : ContinuousOn (fun u => inner ℝ (g u) (z u)) S := hg.inner hc
  have hif : ContinuousOn (fun u => (inner ℝ (f u) (z u)) • f u) S := hi.smul hf
  have hjg : ContinuousOn (fun u => (inner ℝ (g u) (z u)) • g u) S := hj.smul hg
  exact (hc.sub hif).sub hjg

lemma unitChartVector_lower (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ unitChartDomain J α hs ht p K,
      m ≤ ‖unitChartVector J α hs ht p u‖ := by
  have hS := (unitChartDomain_closed J α hs ht p hK hKT).isCompact
  have hc := (unitChartVector_continuousOn J α hs ht p hKT).norm
  have hp : ∀ u ∈ unitChartDomain J α hs ht p K, 0 < ‖unitChartVector J α hs ht p u‖ :=
    fun u hu => norm_pos_iff.mpr (unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1)
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn (hc.inv₀ (fun u hu => ne_of_gt (hp u hu)))
  refine ⟨(max M 1)⁻¹,by positivity,fun u hu => ?_⟩
  have hm := hM u hu
  change ‖‖unitChartVector J α hs ht p u‖⁻¹‖ ≤ M at hm
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hp u hu))] at hm
  exact (inv_le_comm₀ (hp u hu) (lt_of_lt_of_le zero_lt_one (le_max_right M 1))).mp
    (hm.trans (le_max_left _ _))
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_TransverseDefectCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
open RadialPotential
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma transverse_graph_sq_bound (K L : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (hL : ∀ v, L (L v) = -v) (z a : V) (ha : a ≠ 0)
    {m C : ℝ} (hm : 0 < m) (hma : m ≤ ‖hermitianGraph K a‖)
    (_hC : 0 ≤ C) (hKL : ‖K-L‖ ≤ C*‖z‖) :
    ‖transverse (first a) (second a (L a)) z‖^2 ≤
      (2/m^2)*hermitianDefect K z a + (2*‖hermitianGraph K‖^2*C^2)*‖z‖^4 := by
  let D := hermitianDefect K z a
  have hD : 0 ≤ D := hermitianDefect_nonneg K hK z a
  have hbase := transverse_graph_bound K L hK hL z a ha
  have h₁ : Real.sqrt D/‖hermitianGraph K a‖ ≤ Real.sqrt D/m :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hm hma
  have h₂ : ‖hermitianGraph K z‖*‖K-L‖ ≤ (‖hermitianGraph K‖*C)*‖z‖^2 := by
    have hh := mul_le_mul ((hermitianGraph K).le_opNorm z) hKL (norm_nonneg _) (by positivity)
    nlinarith
  have hh : ‖transverse (first a) (second a (L a)) z‖ ≤ Real.sqrt D/m+(‖hermitianGraph K‖*C)*‖z‖^2 :=
    hbase.trans (add_le_add h₁ h₂)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hs : (Real.sqrt D/m)^2 = D/m^2 := by rw [div_pow,Real.sq_sqrt hD]
  have hcross := sq_nonneg (Real.sqrt D/m-(‖hermitianGraph K‖*C)*‖z‖^2)
  change _ ≤ (2/m^2)*D+_
  rw [div_mul_eq_mul_div]
  have he : 2*D/m^2 = 2*(D/m^2) := by ring
  rw [he]
  nlinarith

lemma defect_quotient_radius_compare {d t g B : ℝ} (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hg : 0 ≤ g) (htg : t ≤ g) (hgt : g ≤ B*t)
    (hz : t = 0 → d = 0) : d/t^4 ≤ B^4*(d/g^4) := by
  by_cases ht0 : t = 0
  · simp [ht0,hz ht0]
  by_cases hg0 : g = 0
  · have : t = 0 := by linarith
    exact (ht0 this).elim
  · have ht4 : 0 < t^4 := pow_pos (lt_of_le_of_ne ht (Ne.symm ht0)) 4
    have hg4 : 0 < g^4 := pow_pos (lt_of_le_of_ne hg (Ne.symm hg0)) 4
    apply (div_le_iff₀ ht4).mpr
    rw [mul_assoc,div_mul_eq_mul_div,← mul_div_assoc]
    apply (le_div_iff₀ hg4).mpr
    have hp := pow_le_pow_left₀ hg hgt 4
    rw [mul_pow] at hp
    nlinarith
end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_UnitTransverseLocal
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
private lemma lipschitzOn_norm_sub_fixed {V W : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] {f : V → W} {S : Set V} {L : NNReal}
    (hL : LipschitzOnWith L f S) {b y : V} (hb : b ∈ S) (hy : y ∈ S) :
    ‖f b-f y‖ ≤ (L:ℝ)*‖y-b‖ := by
  have hh := hL.dist_le_mul b hb y hy
  simpa only [dist_eq_norm,norm_sub_rev] using hh

namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma unitTransverse_local_bound (p : X) (b : Space) {R : ℝ} (hR : 0 < R)
    (hBT : Metric.closedBall b R ⊆ (extChartAt Model p).target) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ u ∈ unitChartDomain J α hs ht p (Metric.closedBall b R),
        ‖unitTransverse J α hs ht p b u‖^2 ≤
          C*unitRadialDefect J α hs ht p b u+B*‖unitChartBase J α hs ht p u-b‖^4 := by
  have hb := hBT (Metric.mem_closedBall_self hR.le)
  obtain ⟨m,hm,hml⟩ := unitChartVector_lower J α hs ht p (isCompact_closedBall b R) hBT
  obtain ⟨L,hL⟩ := ((coordinateJ_smooth J p).mono hBT).exists_lipschitzOnWith
    (by simp) (convex_closedBall b R) (isCompact_closedBall b R)
  let G := hermitianGraph (coordinateJ J p b)
  refine ⟨2/m^2,2*‖G‖^2*(L:ℝ)^2,by positivity,by positivity,fun u hu => ?_⟩
  have hu' := unitChart_mem J α hs ht p hBT hu
  have hcomp : ‖coordinateJ J p b-coordinateJ J p (unitChartBase J α hs ht p u)‖ ≤
      (L:ℝ)*‖unitChartBase J α hs ht p u-b‖ :=
    lipschitzOn_norm_sub_fixed hL (Metric.mem_closedBall_self hR.le) hu'.2
  exact transverse_graph_sq_bound _ _ (coordinateJ_square J p hb)
    (coordinateJ_square J p (hBT hu'.2)) _ _ (unitChartVector_ne_zero J α hs ht p u hu'.1)
    hm ((hml u hu).trans (hermitianGraph_norm_ge _ _)) L.coe_nonneg hcomp
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefectCombination
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompactSpace X] [T2Space X] in
lemma smoothUnitDefect_nonneg (p : X) {b : Space} (hb : b ∈ (extChartAt Model p).target)
    (r s : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ smoothUnitDefect J α hs ht p b r s u :=
  Set.indicator_nonneg (fun v _ => div_nonneg
    (mul_nonneg (by norm_num) (unitRadialDefect_nonneg J α hs ht p hb v)) (sq_nonneg _)) u

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransverseCut
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] in
lemma unitTransverseCut_measurable (p : X) (b : Space) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (unitTransverseCut J α hs ht p b K) := by
  classical
  exact (unitTransverse_continuousOn J α hs ht p b hKT).measurable_piecewise continuousOn_const
    (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] in
lemma unitDistanceCut_measurable (p : X) (b : Space) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (unitDistanceCut J α hs ht p b K) := by
  classical
  exact ((unitChartBase_continuousOn J α hs ht p hKT).sub continuousOn_const).norm.measurable_piecewise
    continuousOn_const (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] [T2Space X] in
lemma unitTransverseCut_zero (p : X) (b : Space) (K : Set Space)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : unitDistanceCut J α hs ht p b K u = 0) :
    unitTransverseCut J α hs ht p b K u = 0 := by
  by_cases h : u ∈ unitChartDomain J α hs ht p K
  · rw [unitDistanceCut,indicator_of_mem h,norm_eq_zero] at hu
    simp only [unitTransverseCut,indicator_of_mem h,unitTransverse,hu,transverse,inner_zero_right,
      zero_smul,sub_zero]
  · exact indicator_of_notMem h _
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransverseIntegrable
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma unitTransverse_quotient_integrable (p : X) (b : Space) {R : ℝ} (hR : 0 < R)
    (hBT : Metric.closedBall b R ⊆ (extChartAt Model p).target)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hdef : Integrable (smoothUnitDefect J α hs ht p b R 0) μ) :
    Integrable (fun u => ‖unitTransverseCut J α hs ht p b K u‖^2 /
      (unitDistanceCut J α hs ht p b K u)^4) μ := by
  obtain ⟨C,B,hC,hB,hlocal⟩ := unitTransverse_local_bound J α hs ht p b hR hBT
  have hb := hBT (Metric.mem_closedBall_self hR.le)
  let G := hermitianGraph (coordinateJ J p b)
  have hmeas := ((unitTransverseCut_measurable J α hs ht p b hK hKT).norm.pow_const 2).div
    ((unitDistanceCut_measurable J α hs ht p b hK hKT).pow_const 4)
  apply ((hdef.const_mul (C*‖G‖^4)).add (integrable_const (B+1/R^2))).mono' hmeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  simp only [Pi.div_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hzero : 0 ≤ smoothUnitDefect J α hs ht p b R 0 u := smoothUnitDefect_nonneg J α hs ht p hb R 0 u
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · simp only [unitTransverseCut,unitDistanceCut,indicator_of_mem hu]
    have husrc := (unitChart_mem J α hs ht p hKT hu).1
    let t := ‖unitChartBase J α hs ht p u-b‖
    let d := unitRadialDefect J α hs ht p b u
    let g := unitRadialRadius J α hs ht p b u
    have ht0 : 0 ≤ t := norm_nonneg _
    have hd0 : 0 ≤ d := unitRadialDefect_nonneg J α hs ht p hb u
    have hg0 : 0 ≤ g := norm_nonneg _
    by_cases hball : u ∈ unitChartDomain J α hs ht p (Metric.closedBall b R)
    · have hfrac := defect_quotient_radius_compare hd0 ht0 hg0
        (hermitianGraph_norm_ge (coordinateJ J p b) (unitChartBase J α hs ht p u-b))
        (G.le_opNorm (unitChartBase J α hs ht p u-b)) (by
          intro hz
          have hz' : unitChartBase J α hs ht p u-b = 0 := norm_eq_zero.mp hz
          simp [d,unitRadialDefect,hz',hermitianDefect])
      have he : smoothUnitDefect J α hs ht p b R 0 u = 2*d/g^4 := by
        rw [smoothUnitDefect,indicator_of_mem hball]
        change 2*d/((0:ℝ)^2+g^2)^2 = 2*d/g^4
        ring
      have hsq := div_le_div_of_nonneg_right (hlocal u hball) (pow_nonneg ht0 4)
      have hnorm : ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ C*(d/t^4)+B*(t^4/t^4) := by
        calc
          _ ≤ (C*d+B*t^4)/t^4 := hsq
          _ = _ := by ring
      have htfrac : t^4/t^4 ≤ 1 := div_self_le_one _
      have hh := hnorm.trans (add_le_add (mul_le_mul_of_nonneg_left hfrac hC)
        (mul_le_of_le_one_right hB htfrac))
      rw [he]
      have hp : 0 ≤ C*‖G‖^4*(d/g^4) := by positivity
      have hRinv : 0 ≤ (1:ℝ)/R^2 := by positivity
      change ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ C*‖G‖^4*(2*d/g^4)+(B+1/R^2)
      rw [show 2*d/g^4 = 2*(d/g^4) by ring]
      nlinarith
    · have hRt : R ≤ t := by
        by_contra h
        have hmem : unitChartBase J α hs ht p u ∈ Metric.closedBall b R := by
          rw [Metric.mem_closedBall,dist_eq_norm]
          exact (lt_of_not_ge h).le
        exact hball ⟨unitChartBase J α hs ht p u,hmem,(extChartAt Model p).left_inv husrc⟩
      have htpos := lt_of_lt_of_le hR hRt
      obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p u husrc
      have hnorm := norm_transverse_le _ _ (unitChartBase J α hs ht p u-b) h₁ h₂ h₃
      have hsq := div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (pow_nonneg ht0 4)
      have he : t^2/t^4 = 1/t^2 := by field_simp
      have hh : ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ 1/R^2 := by
        apply (hsq.trans_eq he).trans
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hR) (pow_le_pow_left₀ hR.le hRt 2)
      have hp : 0 ≤ C*‖G‖^4*smoothUnitDefect J α hs ht p b R 0 u := by positivity
      change ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ C*‖G‖^4*smoothUnitDefect J α hs ht p b R 0 u+(B+1/R^2)
      linarith
  · simp only [unitTransverseCut,unitDistanceCut,indicator_of_notMem hu,norm_zero]
    have hp : 0 ≤ C*‖G‖^4*smoothUnitDefect J α hs ht p b R 0 u := by positivity
    simp only [zero_pow (by decide : 2 ≠ 0),zero_div]
    positivity
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricQuadraticMass
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem separating_probability_quadratic_growth
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
        hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ C*s^2 := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  apply local_chart_mass_to_riemannian (fun u : MetricUnit g => u.val.proj) μ
  intro x
  obtain ⟨p,R,C,r,hx,hR,hC,hr,_hrR,h4,hm⟩ := separating_probability_local_quadratic J α hs ht μ hann x
  exact ⟨p,R,C,r,hx,hR,hC,hr,h4,hm⟩
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShellLimit
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma profile_le_one (r : ℝ) (d : ℝ≥0∞) : profile r d ≤ 1 := by
  apply pow_le_one₀ bot_le
  exact ENNReal.inv_le_one.mpr le_self_add

lemma measurable_profile {Y : Type*} [MeasurableSpace Y]
    (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    Measurable (fun y => profile r (δ y)) := by
  unfold profile
  fun_prop

lemma integral_profile_toReal {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    (∫ y, (profile r (δ y)).toReal ∂μ) = (∫⁻ y, profile r (δ y) ∂μ).toReal := by
  exact integral_toReal (measurable_profile δ hδ r).aemeasurable
    (Eventually.of_forall fun y => (profile_le_one r (δ y)).trans_lt (by simp))

lemma integral_profile_normalized_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) : (∫ y, (profile r (δ y)).toReal ∂μ)/r^2 ≤ 8*C := by
  rw [integral_profile_toReal μ δ hδ r]
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_profile_le μ δ hδ C hC hgrowth hr)
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr hle

end QuadraticShell

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma geometric_edist_eq (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) :
    let := geometricMetricSpace J α hs ht
    edist x y = hermitianEDist J α hs ht x y := rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

namespace TamingCompatibility.RiemannianChartDistance
open Bundle Manifold Set Metric _root_.MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) 1 X]
  [RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.RiemannianChartDistance.inverseChartNormedAddCommGroup
lemma chart_segment_bound (p : X) (K : Set E) (hconv : Convex ℝ K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ,E) p).target) (C : ℝ≥0)
    (hC : ∀ z ∈ K, ‖mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm z‖ₑ ≤ C)
    {q r : E} (hq : q ∈ K) (hr : r ∈ K) :
    riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm q)
      ((extChartAt 𝓘(ℝ,E) p).symm r) ≤ C*edist q r := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) q r
  let γ := (extChartAt 𝓘(ℝ,E) p).symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' K := by
    rw [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,← segment_eq_image_lineMap]
    exact hconv.segment_subset hq hr
  have hηs : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 η (Icc 0 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact η.contDiff.contDiffOn
  have hb : riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm q)
      ((extChartAt 𝓘(ℝ,E) p).symm r) ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηs (hη.trans (preimage_mono hK))
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply hb.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have he : mfderiv[Icc 0 1] γ t =
      (mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hK (hη ht))
    · exact hηs.mdifferentiableOn one_ne_zero t ht
    · exact (hη.trans (preimage_mono hK)).trans (preimage_mono (extChartAt_target_subset_range p))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hev : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congrArg (fun L => L 1) he
  rw [hev]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  apply mul_le_mul (hC (η t) (hη ht))
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl
  · exact bot_le
  · exact bot_le

end TamingCompatibility.RiemannianChartDistance

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms ManifoldVolume Set Filter Metric
open scoped Manifold ContDiff Topology NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
include hs in
lemma chartMetric_norm_continuousOn (p : X) :
    ContinuousOn (fun z => ‖chartMetric J α p z‖) (extChartAt Model p).target := by
  let : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hh : ContinuousOn (chartMetric J α p) (extChartAt Model p).target :=
    ((hs.invariantPart J).metricCoords J p).continuousOn
  exact (continuous_norm : Continuous (norm : (Space →L[ℝ] Space →L[ℝ] ℝ) → ℝ)).comp_continuousOn hh

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  TamingCompatibility.RiemannianChartDistance.inverseChartNormedAddCommGroup

lemma inverseChart_opNorm (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
    ‖mfderivWithin Model Model (extChartAt Model p).symm (Set.range Model) z‖ ≤ Real.sqrt ‖chartMetric J α p z‖ := by
  dsimp only
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
  rw [show Set.range Model = univ by simp [Model],mfderivWithin_univ]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  have he : ‖mfderiv Model Model (extChartAt Model p).symm z u‖^2 = chartMetric J α p z u u := by
    exact (real_inner_self_eq_norm_sq _).symm.trans
      (chartMetric_derivative J α p hz u u).symm
  have hb : chartMetric J α p z u u ≤ ‖chartMetric J α p z‖*‖u‖^2 := by
    calc
      _ ≤ ‖chartMetric J α p z u u‖ := le_abs_self _
      _ ≤ ‖chartMetric J α p z‖*‖u‖*‖u‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  rw [mul_pow,Real.sq_sqrt (norm_nonneg (chartMetric J α p z))]
  exact he.trans_le hb

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma chartInverse_locallyLipschitz (p : X) :
    let := geometricMetricSpace J α hs ht
    LocallyLipschitzOn (extChartAt Model p).target (extChartAt Model p).symm := by
  dsimp only
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let := geometricMetricSpace J α hs ht
  intro z hz
  have hc : ContinuousAt (fun y => ‖chartMetric J α p y‖) z :=
    (chartMetric_norm_continuousOn J α hs p).continuousAt
      ((isOpen_extChartAt_target p).mem_nhds hz)
  let C := Real.sqrt (‖chartMetric J α p z‖+1)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hn : {y | ‖chartMetric J α p y‖ < ‖chartMetric J α p z‖+1} ∈ 𝓝 z :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_extChartAt_target p).mem_nhds hz) hn)
  refine ⟨⟨C,hC⟩,Metric.ball z r,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr),?_⟩
  intro q hq y hy
  change hermitianEDist J α hs ht _ _ ≤ _
  apply RiemannianChartDistance.chart_segment_bound p _ (convex_ball z r)
    (fun _ h => (hrsub h).1) ⟨C,hC⟩ ?_ hq hy
  intro w hw
  have hb := (inverseChart_opNorm J α hs ht p (hrsub hw).1).trans
    (Real.sqrt_le_sqrt (le_of_lt (hrsub hw).2))
  exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hb)

lemma chartInverse_compact_lipschitz (p : X) (K : Set Space)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt Model p).target) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt Model p).symm K := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    ((chartInverse_locallyLipschitz J α hs ht p).mono hKt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactProfilePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.Concentration
lemma sum_six_le (r t : ℝ) : (r+t)^6 ≤ 8*(r^2+t^2)^3 := by
  have h₁ : (r+t)^2 ≤ 2*(r^2+t^2) := by nlinarith [sq_nonneg (r-t)]
  have hh := pow_le_pow_left₀ (sq_nonneg (r+t)) h₁ 3
  calc
    (r+t)^6 = ((r+t)^2)^3 := by ring
    _ ≤ (2*(r^2+t^2))^3 := hh
    _ = _ := by ring

lemma radialCoefficient_quadratic_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t*t^2 ≤ (8/r^2)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^2)*(r^6/(r+t)^6) = 8*r^4/(r+t)^6 := by field_simp
  rw [he',div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : t^2 ≤ r^2+t^2 := by nlinarith [sq_nonneg r]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ t^2)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^4)
  nlinarith
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransverseLimit
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma unitTransverse_rational_limit (p : X) (b : Space) {R : ℝ} (hR : 0 < R)
    (hBT : Metric.closedBall b R ⊆ (extChartAt Model p).target)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hdef : Integrable (smoothUnitDefect J α hs ht p b R 0) μ) :
    Tendsto (fun r : ℝ => ∫ u, radialCoefficient r (unitDistanceCut J α hs ht p b K u)*
      ‖unitTransverseCut J α hs ht p b K u‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply rational_defect_tendsto_zero _ _
    ((unitTransverseCut_measurable J α hs ht p b hK hKT).norm.pow_const 2)
    (unitDistanceCut_measurable J α hs ht p b hK hKT) (fun _ => by positivity)
    (fun u hu => by rw [unitTransverseCut_zero J α hs ht p b K u hu,norm_zero]; norm_num)
  exact unitTransverse_quotient_integrable J α hs ht p b hR hBT hK hKT μ hdef

lemma separating_probability_atlas_transverse_limit
    (A : FiniteCharts X) (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) (x : X) (hp : A.partition p x ≠ 0)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ u,
      radialCoefficient r (unitDistanceCut J α hs ht p.val (extChartAt Model p.val x) K u)*
        ‖unitTransverseCut J α hs ht p.val (extChartAt Model p.val x) K u‖^2 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨R,hR,hBT,hdef⟩ := separating_probability_atlas_defect J α hs ht A D hA μ hann p x hp
  exact unitTransverse_rational_limit J α hs ht p.val _ hR hBT hK hKT μ hdef
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma unitTransverse_rational_measurable (p : X) (b : Space)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target) (r : ℝ) :
    Measurable (fun u => radialCoefficient r (unitDistanceCut J α hs ht p b K u)*
      ‖unitTransverseCut J α hs ht p b K u‖^2) := by
  have hd := unitDistanceCut_measurable J α hs ht p b hK hKT
  have hv := unitTransverseCut_measurable J α hs ht p b hK hKT
  exact (measurable_const.div ((measurable_const.add (hd.pow_const 2)).pow_const 4)).mul (hv.norm.pow_const 2)

lemma separating_probability_transverse_uniform
    (p : X) {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, x ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → ∀ r : ℝ, 0 < r →
      Integrable (fun u => radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
        ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2) μ ∧
      (∫ u, radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
        ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2 ∂μ) ≤ C := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  obtain ⟨L₀,hL₀⟩ := chartInverse_compact_lipschitz J α hs ht p K hK hKT
  let L : ℝ := (L₀:ℝ)+1
  have hL : 0 < L := by dsimp [L] <;> positivity
  refine ⟨64*M*L^2,by positivity,fun x hx hxK r hr => ?_⟩
  let P : MetricUnit (hermitianMetric J α hs ht) → ℝ :=
    fun u => ((1+dist x u.val.proj/(L*r))⁻¹)^6
  have hLr : 0 < L*r := mul_pos hL hr
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hp : Continuous P := ((continuous_const.add ((continuous_const.dist hb).div_const (L*r))).inv₀
    (fun u => (show 0 < 1+dist x u.val.proj/(L*r) by positivity).ne')).pow 6
  have hpi : Integrable P μ := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (u : MetricUnit (hermitianMetric J α hs ht)) :
      radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
        ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2 ≤ (8/r^2)*P u := by
    by_cases hu : u ∈ unitChartDomain J α hs ht p K
    · rw [unitDistanceCut,unitTransverseCut,indicator_of_mem hu,indicator_of_mem hu]
      have humem := unitChart_mem J α hs ht p hKT hu
      obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p u humem.1
      have hv := norm_transverse_le (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u)
        (unitChartBase J α hs ht p u-extChartAt Model p x) h₁ h₂ h₃
      have hphys := hL₀.dist_le_mul _ hxK _ humem.2
      change dist ((extChartAt Model p).symm (extChartAt Model p x))
        ((extChartAt Model p).symm (unitChartBase J α hs ht p u)) ≤ _ at hphys
      simp only [unitChartBase] at hphys
      rw [(extChartAt Model p).left_inv hx,(extChartAt Model p).left_inv humem.1,dist_eq_norm,norm_sub_rev] at hphys
      have htransport : dist x u.val.proj ≤ L*‖unitChartBase J α hs ht p u-extChartAt Model p x‖ :=
        hphys.trans (mul_le_mul_of_nonneg_right (by dsimp [L] <;> linarith) (norm_nonneg _))
      have hdiv : dist x u.val.proj/(L*r) ≤ ‖unitChartBase J α hs ht p u-extChartAt Model p x‖/r := by
        apply (div_le_iff₀ hLr).mpr
        calc
          _ ≤ L*‖unitChartBase J α hs ht p u-extChartAt Model p x‖ := htransport
          _ = _ := by field_simp
      have hpro : ((1+‖unitChartBase J α hs ht p u-extChartAt Model p x‖/r)⁻¹)^6 ≤ P u := by
        exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 6
      calc
        _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p u-extChartAt Model p x‖*
            ‖unitChartBase J α hs ht p u-extChartAt Model p x‖^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (radialCoefficient_nonneg _ _)
        _ ≤ (8/r^2)*((1+‖unitChartBase J α hs ht p u-extChartAt Model p x‖/r)⁻¹)^6 :=
          radialCoefficient_quadratic_profile hr (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpro (by positivity)
    · rw [unitTransverseCut,indicator_of_notMem hu,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      positivity
  have hi : Integrable (fun u => radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
      ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2) μ := by
    apply (hpi.const_mul (8/r^2)).mono' (unitTransverse_rational_measurable J α hs ht p _ hK hKT r).aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _))]
      exact hbound u
  refine ⟨hi,?_⟩
  have hg : ∀ s : ℝ, 0 < s → μ.real {u | ENNReal.ofReal (dist x u.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro s hsp
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hsp
  have hm : Measurable (fun u : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist x u.val.proj)) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
  have hq := QuadraticShell.integral_profile_normalized_bound μ
    (fun u : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist x u.val.proj)) hm M hM hg hLr
  have he (u : MetricUnit (hermitianMetric J α hs ht)) :
      (QuadraticShell.profile (L*r) (ENNReal.ofReal (dist x u.val.proj))).toReal = P u := by
    rw [QuadraticShell.profile_ofReal hLr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
  simp_rw [he] at hq
  have hqi := (div_le_iff₀ (sq_pos_of_pos hLr)).mp hq
  calc
    _ ≤ ∫ u, (8/r^2)*P u ∂μ := integral_mono hi (hpi.const_mul _) hbound
    _ = (8/r^2)*(∫ u, P u ∂μ) := integral_const_mul _ _
    _ ≤ (8/r^2)*(8*M*(L*r)^2) := mul_le_mul_of_nonneg_left hqi (by positivity)
    _ = _ := by field_simp <;> ring
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma angularBase_continuous : Continuous (angularBase J α hs ht) := by
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  exact (hb.comp continuous_snd).prodMk (hb.comp continuous_fst)

attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransversePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma transversePairKernel_measurable (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) {r : ℝ} (hr : 0 < r) :
    Measurable (transversePairKernel A J α hs ht p K r) := by
  classical
  let S := unitChartDomain J α hs ht p.val K
  let f := fun uv : UnitPair J α hs ht => unitChartFirst J α hs ht p.val uv.2
  let g := fun uv : UnitPair J α hs ht => unitChartSecond J α hs ht p.val uv.2
  let z := fun uv : UnitPair J α hs ht => unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1
  have hf : ContinuousOn f (S ×ˢ S) := (unitChartFirst_continuousOn J α hs ht p.val hKT).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg : ContinuousOn g (S ×ˢ S) := (unitChartSecond_continuousOn J α hs ht p.val hKT).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hb := unitChartBase_continuousOn J α hs ht p.val hKT
  have hz : ContinuousOn z (S ×ˢ S) := (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub
    (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hi : ContinuousOn (fun uv => inner ℝ (f uv) (z uv)) (S ×ˢ S) := hf.inner hz
  have hj : ContinuousOn (fun uv => inner ℝ (g uv) (z uv)) (S ×ˢ S) := hg.inner hz
  have hiv : ContinuousOn (fun uv => (inner ℝ (f uv) (z uv)) • f uv) (S ×ˢ S) := hi.smul hf
  have hjv : ContinuousOn (fun uv => (inner ℝ (g uv) (z uv)) • g uv) (S ×ˢ S) := hj.smul hg
  have hv : ContinuousOn (fun uv => unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2) (S ×ˢ S) := (hz.sub hiv).sub hjv
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.1.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).snd).continuousOn
  have hk : ContinuousOn (fun uv => radialCoefficient r ‖z uv‖) (S ×ˢ S) :=
    continuousOn_const.div ((continuousOn_const.add (hz.norm.pow 2)).pow 4) (fun uv _ => by positivity)
  have hm := ((ha.mul hk).mul (hv.norm.pow 2)).measurable_piecewise
      (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) (S ×ˢ S)ᶜ)
      ((unitChartDomain_closed J α hs ht p.val hK hKT).prod
        (unitChartDomain_closed J α hs ht p.val hK hKT)).measurableSet
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext uv
  by_cases hu : uv ∈ S ×ˢ S <;>
    simp [transversePairKernel, Set.indicator, Set.piecewise, S, z] at hu ⊢

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_apply (p : A.centers) (K : Set Space) (r : ℝ)
    (u v : MetricUnit (hermitianMetric J α hs ht)) :
    transversePairKernel A J α hs ht p K r (u,v) =
      (unitChartDomain J α hs ht p.val K).indicator
        (fun w => A.partition p w.val.proj* (radialCoefficient r
          (unitDistanceCut J α hs ht p.val (unitChartBase J α hs ht p.val w) K v)*
          ‖unitTransverseCut J α hs ht p.val (unitChartBase J α hs ht p.val w) K v‖^2)) u := by
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val K
  · rw [indicator_of_mem hu]
    by_cases hv : v ∈ unitChartDomain J α hs ht p.val K
    · simp only [transversePairKernel,indicator_of_mem (show (u,v) ∈ _ ×ˢ _ from ⟨hu,hv⟩),
        unitDistanceCut,unitTransverseCut,indicator_of_mem hv]
      ring
    · simp [transversePairKernel,Set.indicator,hu,hv,unitDistanceCut,unitTransverseCut]
  · simp [transversePairKernel,Set.indicator,hu]
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma separating_probability_transverse_pair_limit
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ u, ∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let S := unitChartDomain J α hs ht p.val K
  let H := fun (r : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) =>
    ∫ v, radialCoefficient r (unitDistanceCut J α hs ht p.val (unitChartBase J α hs ht p.val u) K v)*
      ‖unitTransverseCut J α hs ht p.val (unitChartBase J α hs ht p.val u) K v‖^2 ∂μ
  have he (r : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
      (∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ) =
        S.indicator (fun w => A.partition p w.val.proj*H r w) u := by
    simp_rw [transversePairKernel_apply]
    by_cases hu : u ∈ S
    · dsimp only [S] at hu
      simp only [S,indicator_of_mem hu]
      exact integral_const_mul _ _
    · dsimp only [S] at hu
      simp only [S,indicator_of_notMem hu,integral_zero]
  obtain ⟨C,hC,huniform⟩ := separating_probability_transverse_uniform J α hs ht p.val hK hKT μ hann
  have hnonneg (r : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
      0 ≤ S.indicator (fun w => A.partition p w.val.proj*H r w) u := by
    apply Set.indicator_nonneg _ u
    intro w _
    apply mul_nonneg (A.partition.nonneg _ _)
    exact integral_nonneg (fun v => mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _))
  have hbound (r : ℝ) (hr : 0 < r) (u : MetricUnit (hermitianMetric J α hs ht)) :
      ‖∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ‖ ≤ C := by
    rw [he,Real.norm_eq_abs,abs_of_nonneg (hnonneg r u)]
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu]
      have humem := unitChart_mem J α hs ht p.val hKT hu
      have hh := (huniform u.val.proj humem.1 humem.2 r hr).2
      calc
        _ ≤ A.partition p u.val.proj*C := mul_le_mul_of_nonneg_left hh (A.partition.nonneg _ _)
        _ ≤ C := mul_le_of_le_one_left hC (A.partition.le_one _ _)
    · rw [indicator_of_notMem hu]
      exact hC
  have hlim (u : MetricUnit (hermitianMetric J α hs ht)) :
      Tendsto (fun r : ℝ => ∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simp_rw [he]
    by_cases hu : u ∈ S
    · simp only [indicator_of_mem hu]
      by_cases hc : A.partition p u.val.proj = 0
      · simp only [hc,zero_mul]
        exact tendsto_const_nhds
      · have hi := separating_probability_atlas_transverse_limit J α hs ht A D hA μ hann
          p u.val.proj hc hK hKT
        simpa only [H,unitChartBase,mul_zero] using tendsto_const_nhds.mul hi
    · simp only [indicator_of_notMem hu]
      exact tendsto_const_nhds
  have hm : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), AEStronglyMeasurable
      (fun u => ∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ) μ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (transversePairKernel_measurable A J α hs ht p hK hKT hr).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hb : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ u ∂μ,
      ‖∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ae_of_all _ (hbound r hr)
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun _ => C) hm hb (integrable_const C) (ae_of_all _ hlim)
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransversePairProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_nonneg (p : A.centers) (K : Set Space) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ transversePairKernel A J α hs ht p K r uv := by
  apply indicator_nonneg _ uv
  intro v _
  exact mul_nonneg (mul_nonneg (A.partition.nonneg _ _) (radialCoefficient_nonneg _ _)) (sq_nonneg _)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_bound (p : A.centers) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p.val).target) {r : ℝ} (hr : 0 < r) (uv : UnitPair J α hs ht) :
    transversePairKernel A J α hs ht p K r uv ≤ 8/r^2 := by
  by_cases huv : uv ∈ (unitChartDomain J α hs ht p.val K) ×ˢ (unitChartDomain J α hs ht p.val K)
  · rw [transversePairKernel,indicator_of_mem huv]
    have hsrc := (unitChart_mem J α hs ht p.val hKT huv.2).1
    obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p.val uv.2 hsrc
    have ht' := norm_transverse_le (unitChartFirst J α hs ht p.val uv.2)
      (unitChartSecond J α hs ht p.val uv.2)
      (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) h₁ h₂ h₃
    have hp : ((1+‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r)⁻¹)^6 ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      apply inv_le_one_of_one_le₀
      have : 0 ≤ ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r := by positivity
      linarith
    calc
      _ = A.partition p uv.1.val.proj*(radialCoefficient r
          ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2) := by ring
      _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2 :=
        mul_le_of_le_one_left (mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _)) (A.partition.le_one _ _)
      _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) (radialCoefficient_nonneg _ _)
      _ ≤ (8/r^2)*((1+‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r)⁻¹)^6 :=
        radialCoefficient_quadratic_profile hr (norm_nonneg _)
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hp
  · rw [transversePairKernel,indicator_of_notMem huv]
    positivity

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma transversePairKernel_integrable (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (transversePairKernel A J α hs ht p K r) (μ.prod μ) := by
  apply (integrable_const (8/r^2)).mono'
    (transversePairKernel_measurable A J α hs ht p hK hKT hr).aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [Real.norm_eq_abs,abs_of_nonneg (transversePairKernel_nonneg A J α hs ht p K r uv)]
  exact transversePairKernel_bound A J α hs ht p hKT hr uv

lemma separating_probability_transverse_product_limit_oai
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ uv, transversePairKernel A J α hs ht p K r uv ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply (separating_probability_transverse_pair_limit A J α hs ht D hA μ hann p hK hKT).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (integral_prod _ (transversePairKernel_integrable A J α hs ht p hK hKT μ hr)).symm
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit_oai.{u_1}
