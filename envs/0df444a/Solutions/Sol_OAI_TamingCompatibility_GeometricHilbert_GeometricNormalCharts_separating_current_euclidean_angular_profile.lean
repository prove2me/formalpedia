-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:24:09.754067+00:00
-- url     : https://prove2.me/submissions/f9fe96d2-d849-4065-a971-a23a74e8b183

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc023
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_euclidean_angular_near_point
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_separating_current_angular_moment
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos
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
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
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
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

lemma wedge_inner (u v a b : V) :
    ⟪wedge u v, wedge a b⟫ = ⟪u, a⟫ * ⟪v, b⟫ - ⟪u, b⟫ * ⟪v, a⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, wedge]
  ring

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_GeometricSeparatingProbability
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

open Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma slice_fderiv_contDiffAt (F : P × V → W) {x : P × V}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y : P × V => fderiv ℝ (fun z => F (y.1,z)) y.2) x := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
      fun y hy => hy.differentiableAt (by norm_num)
  apply (dpos_contDiffAt F x hF).congr_of_eventuallyEq
  filter_upwards [hd] with y hy
  exact (dpos_eq_at F y.1 y.2 hy).symm

end TamingCompatibility.GeometricHilbert.UniformJets

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WedgeTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.UnitaryFrame
open FormMetric

lemma norm_wedge_orthonormal (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖wedge u v‖ = 1 := by
  have h := wedge_inner u v u v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hu,hv,huv,zero_mul,sub_zero,one_pow,mul_one] at h
  nlinarith [norm_nonneg (wedge u v)]

end TamingCompatibility.UnitaryFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus

section MatrixFamilies
open UniformJets
open scoped ContDiff
variable {P V W Q ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma firstMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => firstMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) j y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      principalMatrix (fun k z => a k (y.1,z)) (fun z => ρ (y.1,z)) i j y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j)
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_joint (q : ι → V →L[ℝ] ℝ) (b : ι → P → W →L[ℝ] W)
    {x : P × V} (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x.1) :
    ContDiffAt ℝ ∞ (fun y : P × V => gauge (halfJet q (fun i => b i y.1)) y.2) x := by
  have he : ContDiffAt ℝ ∞ (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W))
      (halfJet q (fun i => b i x.1) x.2) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  apply he.comp x
  simp only [halfJet, sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContDiffAt.sum fun i _ =>
    ((q i).contDiff.contDiffAt.comp x contDiffAt_snd).smul
      (((hb i).comp x contDiffAt_fst).const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

attribute [local irreducible] normalFirst

lemma normalGauge_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalGauge J α ht p D g B) x := by
  have hc : ContDiffAt ℝ ∞ (fun q : Space => (q,(0 : Space))) x.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf (i : Fin 4) : ContDiffAt ℝ ∞
      (fun q : Space => normalFirst J α ht p D g B i (q,0)) x.1 := by
    have hi : ContDiffAt ℝ ∞ (normalFirst J α ht p D g B i) (x.1,0) :=
      normalFirst_smooth J α ht p D g B hs hg hB hx i
    exact hi.comp x.1 hc
  exact gauge_joint (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun i q => normalFirst J α ht p D g B i (q,0)) (x := x) hf

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
lemma actual {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    ActualData J α ht p D.chart q D.metricExtension D.frameExtension :=
  ⟨D.actualDomain,D.actual_open,D.centers_actual hq,D.actual_subset,
    D.metric_actual,D.frame_actual,D.metric_symmetric⟩

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma coordinateDecode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateDecode J α ht A D p) (D p).chart.domain := by
  have hmass := (((squareMass_inv_smooth A).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p.val)).contDiffOn).mono (D p).chart.domain_subset
  have hsum : ContDiffOn ℝ ∞ (fun q => ∑ i : A.centers × Fin 6,
      (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
        (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q))
      (D p).chart.domain := by
    apply ContDiffOn.sum
    intro i _
    exact contDiffOn_const.smulRight (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
      (globalFrame_smooth J α ht A D hD hs i.1 i.2))
  exact hmass.smul hsum

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

lemma liftSet_source (p : X) (K : Set (E × E))
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    liftSet p K ⊆ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨(extChartAt I p).map_target (hK hz).1,(extChartAt I p).map_target (hK hz).2⟩

lemma liftSet_compact (p : X) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    IsCompact (liftSet p K) := by
  apply hc.image_of_continuousOn
  exact ((continuousOn_extChartAt_symm p).comp continuousOn_fst (fun z hz => (hK hz).1)).prodMk
    ((continuousOn_extChartAt_symm p).comp continuousOn_snd (fun z hz => (hK hz).2))

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma physicalCompact_target (p : A.centers) :
    (D p).physicalCompact ⊆ (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target :=
  fun _ hz => ⟨(D p).chart.domain_subset ((D p).physicalCompact_domain hz).1,
    (D p).chart.domain_subset ((D p).physicalCompact_domain hz).2⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hs hE in
lemma unitFrameDirection_continuous : Continuous (unitFrameDirection A J α ht E g) := by
  apply continuous_pi
  intro i
  exact (unitEvaluation J g (globalFrame J α ht A E i.1 i.2)
    (globalFrame_smooth J α ht A E hE hs i.1 i.2)).continuous

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
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
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ENNReal Topology
namespace TamingCompatibility.FourthShell
open QuadraticShell
lemma dyadic_term_identity (C r : ℝ) (n : ℕ) :
    (1/64:ℝ)^n*(C*(2^(n+1)*r)^4) = 16*C*r^4*(1/4:ℝ)^n := by
  have hpow : ((2:ℝ)^n)^4 = ((2:ℝ)^4)^n := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ = 16*C*r^4*((1/64:ℝ)^n*((2:ℝ)^4)^n) := by rw [pow_succ,←hpow]; ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem lintegral_profile_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^4)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ENNReal.ofReal (32*C*r^4) := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  have hi (n : ℕ) : ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal (16*C*r^4*(1/4:ℝ)^n) := by
    rw [lintegral_indicator_const (measurableSet_lt hδ measurable_const)]
    have hm : μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} ≤
        ENNReal.ofReal (C*(2^(n+1)*r)^4) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hgrowth _ (by positivity))
    calc
      _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) * ENNReal.ofReal (C*(2^(n+1)*r)^4) :=
        by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), dyadic_term_identity]
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (16*C*r^4*(1/4:ℝ)^n) := ENNReal.tsum_le_tsum hi
    _ = ENNReal.ofReal (16*C*r^4) * (1-ENNReal.ofReal (1/4))⁻¹ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 16*C*r^4), ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/4)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (32*C*r^4) := by
      have hratio : (1-ENNReal.ofReal (1/4))⁻¹ ≤ ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/4)]
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1-1/4)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      calc
        _ ≤ ENNReal.ofReal (16*C*r^4)*ENNReal.ofReal 2 := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end TamingCompatibility.FourthShell

end
end

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

omit [CompactSpace X] in
lemma angularDomain_closed (p : A.centers) : _root_.IsClosed (angularDomain A J α hs ht E p) :=
  ((ManifoldKernelExtension.liftSet_compact p.val _ (E p).physicalCompact_compact
    (physicalCompact_target J α ht A E p)).isClosed).preimage (angularBase_continuous J α hs ht)

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularChartCoordinates A J α hs ht p uv ∈ (E p).physicalCompact := by
  obtain ⟨w,hw,he⟩ := huv
  have he' := congrArg (fun xy : X × X => (extChartAt Model p.val xy.1,extChartAt Model p.val xy.2)) he
  have ht' := physicalCompact_target J α ht A E p hw
  simp only [(extChartAt Model p.val).right_inv ht'.1,(extChartAt Model p.val).right_inv ht'.2] at he'
  change w = angularChartCoordinates A J α hs ht p uv at he'
  rw [← he']
  exact hw

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_source (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    uv.2.val.proj ∈ (extChartAt Model p.val).source ∧ uv.1.val.proj ∈ (extChartAt Model p.val).source :=
  ManifoldKernelExtension.liftSet_source p.val _ (physicalCompact_target J α ht A E p) huv

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularCoordinates A J α hs ht E p uv ∈ (E p).normalCompact := by
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  unfold angularCoordinates
  rw [← he,(E p).normalChart.left_inv ((E p).normalCompact_source hz)]
  exact hz

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_chart (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    (E p).normalChart (angularCoordinates A J α hs ht E p uv) =
      angularChartCoordinates A J α hs ht p uv := by
  apply (E p).normalChart.right_inv
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  rw [← he]
  exact (E p).normalChart.map_source ((E p).normalCompact_source hz)

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_continuousOn (p : A.centers) :
    ContinuousOn (angularChartCoordinates A J α hs ht p) (angularDomain A J α hs ht E p) := by
  have hb := angularBase_continuous J α hs ht
  exact ((continuousOn_extChartAt p.val).comp hb.fst.continuousOn
      (fun _ h => (angularChartCoordinates_source A J α hs ht E p h).1)).prodMk
    ((continuousOn_extChartAt p.val).comp hb.snd.continuousOn
      (fun _ h => (angularChartCoordinates_source A J α hs ht E p h).2))

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_continuousOn (p : A.centers) :
    ContinuousOn (angularCoordinates A J α hs ht E p) (angularDomain A J α hs ht E p) := by
  apply (E p).normalChart.symm.continuousOn.comp (angularChartCoordinates_continuousOn A J α hs ht E p)
  intro uv huv
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  rw [← he]
  exact (E p).normalChart.map_source ((E p).normalCompact_source hz)

include hE in
lemma angularWeight_continuousOn (p : A.centers) :
    ContinuousOn (angularWeight A J α hs ht E p) (angularDomain A J α hs ht E p) := by
  let z := angularCoordinates A J α hs ht E p
  have hz := angularCoordinates_continuousOn A J α hs ht E p
  have hy := angularChartCoordinates_continuousOn A J α hs ht E p
  have hg : ContinuousOn (fun uv => normalGauge J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension (z uv)) (angularDomain A J α hs ht E p) := by
    intro uv huv
    have hx := angularCoordinates_mem A J α hs ht E p huv
    have hn := (((E p).actual hx.1).center J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension).1
    change ((z uv).1,0) ∈ normalDomain J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension at hn
    have hhg : ContinuousAt (normalGauge J α ht p.val (E p).chart (E p).metricExtension
      (E p).frameExtension) (z uv) := (normalGauge_smooth J α ht p.val (E p).chart (E p).metricExtension
      (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth hn).continuousAt
    exact hhg.comp_continuousWithinAt (hz uv huv)
  have hdu := ((coordinateDecode_smooth J α ht A E hE hs p).continuousOn.comp hy.snd
    (fun uv huv => ((E p).physicalCompact_domain (angularChartCoordinates_mem A J α hs ht E p huv)).2)).clm_apply
      (((unitFrameDirection_continuous A J α hs ht E hE _).comp continuous_fst).continuousOn)
  have hdv := ((coordinateDecode_smooth J α ht A E hE hs p).continuousOn.comp hy.fst
    (fun uv huv => ((E p).physicalCompact_domain (angularChartCoordinates_mem A J α hs ht E p huv)).1)).clm_apply
      (((unitFrameDirection_continuous A J α hs ht E hE _).comp continuous_snd).continuousOn)
  have ha := (hdu.sub (hg.clm_apply hdv)).norm.pow 2
  have hw := (((coordinatePartition_smooth_compact A p).1.continuous.comp_continuousOn hz.fst).mul
    ((E p).normalCutoff.continuous.comp_continuousOn hz.snd)).mul ha
  apply hw.congr
  intro uv huv
  have he := angularCoordinates_chart A J α hs ht E p huv
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change (z uv).1 = (angularChartCoordinates A J α hs ht p uv).1 at he1
  change normalMap (E p).metricExtension (E p).frameExtension (z uv).1 (z uv).2 =
    (angularChartCoordinates A J α hs ht p uv).2 at he2
  dsimp only [angularWeight,normalAngular,unitCoordinate,Function.comp_def,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply]
  rw [he2,he1]

omit [CompactSpace X] in
lemma angularNearSet_closed (r : ℝ) (p : A.centers) : _root_.IsClosed (angularNearSet A J α hs ht E r p) :=
  (angularCoordinates_continuousOn A J α hs ht E p).snd.norm.preimage_isClosed_of_isClosed
    (angularDomain_closed A J α hs ht E p) isClosed_Iic

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma angularNear_integrable (r : ℝ) (p : A.centers)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (angularNear A J α hs ht E r p) (μ.prod μ) := by
  have hc := angularNearSet_closed A J α hs ht E r p
  apply (integrable_indicator_iff hc.measurableSet).mpr
  exact ContinuousOn.integrableOn_compact hc.isCompact
    ((angularWeight_continuousOn A J α hs ht E hE p).mono inter_subset_left)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeMassUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_integrable {r : ℝ} (hr : 0 < r)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    let := geometricMetricSpace J α hs ht
    Integrable (fun uv : UnitPair J α hs ht => ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6) (μ.prod μ) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  have hb := angularBase_continuous J α hs ht
  have h : Continuous (fun uv : UnitPair J α hs ht => ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6) :=
    (continuous_const.add ((hb.snd.dist hb.fst).div_const r)).inv₀ (fun uv => by
      have : 0 < 1+dist uv.1.val.proj uv.2.val.proj/r := by positivity
      exact this.ne') |>.pow 6
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_integral_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (M : ℝ) (hM : 0 ≤ M)
    (hgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u | hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ M*s^2)
    {r : ℝ} (hr : 0 < r) :
    let := geometricMetricSpace J α hs ht
    (∫ uv : UnitPair J α hs ht, ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6 ∂μ.prod μ) ≤ 8*M*r^2 := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hi := physicalProfile_integrable J α hs ht hr μ
  rw [integral_prod _ hi]
  have hbnd (u : MetricUnit (hermitianMetric J α hs ht)) :
      (∫ v, ((1+dist u.val.proj v.val.proj/r)⁻¹)^6 ∂μ) ≤ 8*M*r^2 := by
    have hg : ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist u.val.proj v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
      intro s hsp
      simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth u.val.proj s hsp
    have hm : Measurable (fun v : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist u.val.proj v.val.proj)) :=
      (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
    have hh := QuadraticShell.integral_profile_normalized_bound μ
      (fun v : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist u.val.proj v.val.proj)) hm M hM hg hr
    have he (v : MetricUnit (hermitianMetric J α hs ht)) :
        (QuadraticShell.profile r (ENNReal.ofReal (dist u.val.proj v.val.proj))).toReal =
          ((1+dist u.val.proj v.val.proj/r)⁻¹)^6 := by
      rw [QuadraticShell.profile_ofReal hr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mp hh
  calc
    _ ≤ ∫ _ : MetricUnit (hermitianMetric J α hs ht), 8*M*r^2 ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _) hbnd
    _ = _ := by rw [integral_const,probReal_univ,one_smul]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [CompactSpace X] in
lemma euclideanNearSet_closed (s : ℝ) (p : A.centers) :
    _root_.IsClosed (euclideanNearSet A J α hs ht E s p) :=
  ((angularChartCoordinates_continuousOn A J α hs ht E p).snd.sub
    (angularChartCoordinates_continuousOn A J α hs ht E p).fst).norm.preimage_isClosed_of_isClosed
      (angularDomain_closed A J α hs ht E p) isClosed_Iic

omit [CompactSpace X] [T2Space X] in
lemma euclideanLine_continuousOn (p : A.centers) :
    ContinuousOn (fun uv : UnitPair J α hs ht =>
      euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2)
      (angularDomain A J α hs ht E p) := by
  let K := Prod.fst '' (E p).physicalCompact ∪ Prod.snd '' (E p).physicalCompact
  have hKt : K ⊆ (extChartAt Model p.val).target := by
    rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).1)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2)
  have hb : ContinuousOn (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      euclideanLine A J α hs ht p u) (unitChartDomain J α hs ht p.val K) := by
    intro u hu
    have hsrc := (unitChart_mem J α hs ht p.val hKt hu).1
    have hn := unitChartVector_ne_zero J α hs ht p.val u hsrc
    have hn' := normalPart_complex_ne_zero _
      (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hsrc)) hn
    have h1 := (unitChartVector_continuousOn J α hs ht p.val hKt u hu)
    have h2 := (unitChartJVector_continuousOn J α hs ht p.val hKt u hu)
    have hf := (first_continuousAt hn).comp_continuousWithinAt h1
    have hsc : ContinuousAt (fun v : Space × Space => second v.1 v.2)
        (unitChartVector J α hs ht p.val u,unitChartJVector J α hs ht p.val u) := second_continuousAt hn hn'
    have hg := ContinuousAt.comp_continuousWithinAt (x := u)
      (g := fun v : Space × Space => second v.1 v.2)
      (f := fun u => (unitChartVector J α hs ht p.val u,unitChartJVector J α hs ht p.val u)) hsc (h1.prodMk h2)
    have hw : Continuous (fun ab : Space × Space => wedge ab.1 ab.2) := by
      unfold wedge
      fun_prop
    exact ContinuousAt.comp_continuousWithinAt (x := u)
      (g := fun ab : Space × Space => wedge ab.1 ab.2)
      (f := fun v => (unitChartFirst J α hs ht p.val v,unitChartSecond J α hs ht p.val v))
      hw.continuousAt (hf.prodMk hg)
  have hf : MapsTo Prod.fst (angularDomain A J α hs ht E p) (unitChartDomain J α hs ht p.val K) := by
    intro uv huv
    have hxy := angularChartCoordinates_mem A J α hs ht E p huv
    have hsrc := (angularChartCoordinates_source A J α hs ht E p huv).2
    exact ⟨unitChartBase J α hs ht p.val uv.1,Or.inr ⟨_,hxy,rfl⟩,(extChartAt Model p.val).left_inv hsrc⟩
  have hg : MapsTo Prod.snd (angularDomain A J α hs ht E p) (unitChartDomain J α hs ht p.val K) := by
    intro uv huv
    have hxy := angularChartCoordinates_mem A J α hs ht E p huv
    have hsrc := (angularChartCoordinates_source A J α hs ht E p huv).1
    exact ⟨unitChartBase J α hs ht p.val uv.2,Or.inl ⟨_,hxy,rfl⟩,(extChartAt Model p.val).left_inv hsrc⟩
  exact (hb.comp continuous_fst.continuousOn hf).sub (hb.comp continuous_snd.continuousOn hg)

omit [CompactSpace X] [T2Space X] in
lemma euclideanAngularWeight_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanAngularWeight A J α hs ht p uv :=
  mul_nonneg (A.partition.nonneg _ _) (sq_nonneg _)

omit [CompactSpace X] [T2Space X] in
lemma euclideanAngularWeight_continuousOn (p : A.centers) :
    ContinuousOn (euclideanAngularWeight A J α hs ht p) (angularDomain A J α hs ht E p) :=
  (((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn).mul
    ((euclideanLine_continuousOn A J α hs ht E p).norm.pow 2)

variable [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma euclideanAngularNear_integrable (s : ℝ) (p : A.centers)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (euclideanAngularNear A J α hs ht E s p) (μ.prod μ) := by
  have hc := euclideanNearSet_closed A J α hs ht E s p
  apply (integrable_indicator_iff hc.measurableSet).mpr
  exact ContinuousOn.integrableOn_compact hc.isCompact
    ((euclideanAngularWeight_continuousOn A J α hs ht E p).mono inter_subset_left)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanNear_physical_distance (p : A.centers) :
    let := geometricMetricSpace J α hs ht
    ∃ L : ℝ, 0 < L ∧ ∀ s : ℝ, 0 < s → ∀ uv ∈ euclideanNearSet A J α hs ht E s p,
      dist uv.1.val.proj uv.2.val.proj ≤ L*s := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let K := Prod.fst '' (E p).physicalCompact ∪ Prod.snd '' (E p).physicalCompact
  have hK : IsCompact K := ((E p).physicalCompact_compact.image continuous_fst).union
    ((E p).physicalCompact_compact.image continuous_snd)
  have hKt : K ⊆ (extChartAt Model p.val).target := by
    rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).1)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2)
  obtain ⟨C,hC⟩ := chartInverse_compact_lipschitz J α hs ht p.val K hK hKt
  refine ⟨(C:ℝ)+1,by positivity,fun s hs' uv huv => ?_⟩
  have hxy := angularChartCoordinates_mem A J α hs ht E p huv.1
  have hsrc := angularChartCoordinates_source A J α hs ht E p huv.1
  have hh := hC.dist_le_mul _ (show (angularChartCoordinates A J α hs ht p uv).2 ∈ K from Or.inr ⟨_,hxy,rfl⟩)
    _ (show (angularChartCoordinates A J α hs ht p uv).1 ∈ K from Or.inl ⟨_,hxy,rfl⟩)
  change dist ((extChartAt Model p.val).symm (extChartAt Model p.val uv.1.val.proj))
    ((extChartAt Model p.val).symm (extChartAt Model p.val uv.2.val.proj)) ≤ _ at hh
  rw [(extChartAt Model p.val).left_inv hsrc.2,(extChartAt Model p.val).left_inv hsrc.1,dist_eq_norm] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left huv.2 C.coe_nonneg).trans
    (mul_le_mul_of_nonneg_right (by linarith) hs'.le))

lemma separating_current_euclidean_near_mass
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s →
      (∫ uv, (euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ)) uv ∂μ.prod μ) ≤ C*s^2 := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨L,hL,hnear⟩ := euclideanNear_physical_distance A J α hs ht E p
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  refine ⟨512*M*L^2,by positivity,fun s hs' => ?_⟩
  let r := L*s
  have hr : 0 < r := mul_pos hL hs'
  let S := euclideanNearSet A J α hs ht E s p
  have hS : MeasurableSet S := (euclideanNearSet_closed A J α hs ht E s p).measurableSet
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (μ.prod μ) := (integrable_const _).indicator hS
  have hp := physicalProfile_integrable J α hs ht hr μ
  have hb (uv : UnitPair J α hs ht) :
      S.indicator (fun _ => (1:ℝ)) uv ≤ 64*((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6 := by
    by_cases huv : uv ∈ S
    · rw [indicator_of_mem huv]
      have hd := hnear s hs' uv huv
      have hdiv : dist uv.1.val.proj uv.2.val.proj/r ≤ 1 := (div_le_one hr).mpr hd
      have hpos : 0 < 1+dist uv.1.val.proj uv.2.val.proj/r := by positivity
      have hinv : (1/2:ℝ) ≤ (1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹ := by
        have hh : (1+dist uv.1.val.proj uv.2.val.proj/r) ≤ 2 := by linarith
        simpa only [one_div] using one_div_le_one_div_of_le hpos hh
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hinv 6
      norm_num only [div_pow,one_pow,show (2:ℝ)^6 = 64 by norm_num] at hh
      linarith
    · rw [indicator_of_notMem huv]
      positivity
  have hh := integral_mono hi (hp.const_mul 64) hb
  rw [integral_const_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left
    (physicalProfile_integral_bound J α hs ht μ M hM hgrowth hr) (by norm_num : (0:ℝ)≤64)
  exact hh.trans (hh'.trans_eq (by dsimp [r] <;> ring))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularNearPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanLine_norm (p : A.centers) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source) : ‖euclideanLine A J α hs ht p u‖ = 1 := by
  obtain ⟨h1,h2,h3,_⟩ := unitChartPlane J α hs ht p.val u hu
  exact norm_wedge_orthonormal _ _ h1 h2 h3

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularWeight_le (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) : euclideanAngularWeight A J α hs ht p uv ≤ 4 := by
  have hsrc := angularChartCoordinates_source A J α hs ht E p huv
  have hh := norm_sub_le (euclideanLine A J α hs ht p uv.1) (euclideanLine A J α hs ht p uv.2)
  rw [euclideanLine_norm A J α hs ht p uv.1 hsrc.2,euclideanLine_norm A J α hs ht p uv.2 hsrc.1] at hh
  have hsq : ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 ≤ 4 := by
    nlinarith [norm_nonneg (euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2)]
  exact (mul_le_mul_of_nonneg_left hsq (A.partition.nonneg p uv.2.val.proj)).trans
    (by have h := A.partition.le_one p uv.2.val.proj; nlinarith)

include hE hD in
lemma separating_current_euclidean_angular_moment
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ s : ℝ, 0 < s →
      (∫ uv, euclideanAngularNear A J α hs ht E s p uv ∂μ.prod μ) ≤ F*s^4 := by
  obtain ⟨C,B,L,ρ₀,hC,hB,hL,hρ₀,hpoint⟩ := euclidean_angular_near_point A J α hs ht E hE p
  obtain ⟨ρ₁,K,hρ₁,hK,hang⟩ := separating_current_angular_moment A J α hs ht E hE D hD μ hann
  obtain ⟨M,hM,hmass⟩ := separating_current_euclidean_near_mass A J α hs ht E μ hann p
  let ρ := min ρ₀ (ρ₁/L)
  have hρ : 0 < ρ := lt_min hρ₀ (div_pos hρ₁ hL)
  let F := C*K*L^4+B*M+4/ρ^4
  have hF : 0 ≤ F := by positivity
  refine ⟨F,hF,fun s hs' => ?_⟩
  have hi := euclideanAngularNear_integrable A J α hs ht E s p μ
  by_cases hsρ : s ≤ ρ
  · have hs₀ : s ≤ ρ₀ := hsρ.trans (min_le_left _ _)
    have hs₁ : L*s ≤ ρ₁ := by simpa only [mul_comm] using (le_div_iff₀ hL).mp (hsρ.trans (min_le_right _ _))
    have hA := angularNear_integrable A J α hs ht E hE (L*s) p μ
    have hS : Integrable ((euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ))) (μ.prod μ) :=
      (integrable_const _).indicator (euclideanNearSet_closed A J α hs ht E s p).measurableSet
    have hh := integral_mono hi ((hA.const_mul C).add (hS.const_mul (B*s^2))) (hpoint s hs' hs₀)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hA.const_mul C) (hS.const_mul (B*s^2)),integral_const_mul,integral_const_mul] at hh
    have hb₁ := mul_le_mul_of_nonneg_left (hang _ (mul_pos hL hs') hs₁ p) hC
    have hb₂ := mul_le_mul_of_nonneg_left (hmass s hs') (mul_nonneg hB (sq_nonneg s))
    apply hh.trans ((add_le_add hb₁ hb₂).trans ?_)
    dsimp [F]
    have hn : 0 ≤ (4/ρ^4)*s^4 := by positivity
    nlinarith
  · have hpt (uv : UnitPair J α hs ht) : euclideanAngularNear A J α hs ht E s p uv ≤ 4 := by
      by_cases huv : uv ∈ euclideanNearSet A J α hs ht E s p
      · rw [euclideanAngularNear,indicator_of_mem huv]
        exact euclideanAngularWeight_le A J α hs ht E p huv.1
      · rw [euclideanAngularNear,indicator_of_notMem huv]; norm_num
    have hh := integral_mono hi (integrable_const 4) hpt
    rw [integral_const,probReal_univ,one_smul] at hh
    have hpow := pow_le_pow_left₀ hρ.le (le_of_lt (lt_of_not_ge hsρ)) 4
    have hlarge : 4 ≤ (4/ρ^4)*s^4 := by
      rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hρ 4)]
      linarith
    apply hh.trans (hlarge.trans ?_)
    dsimp [F]
    have hn : 0 ≤ (C*K*L^4+B*M)*s^4 := by positivity
    nlinarith
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthWeightedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ENNReal Topology
namespace TamingCompatibility.FourthShell
open QuadraticShell
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

lemma weighted_profile_bound (w d : Y → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ y, 0 ≤ w y) (hd0 : ∀ y, 0 ≤ d y) (hwi : Integrable w μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s →
      (∫ y, {y | d y ≤ s}.indicator w y ∂μ) ≤ C*s^4)
    {r : ℝ} (hr : 0 < r) :
    (∫ y, w y*((1+d y/r)⁻¹)^6 ∂μ) ≤ 32*C*r^4 := by
  let ν := μ.withDensity (fun y => ENNReal.ofReal (w y))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hchange (f : Y → ℝ) : (∫ y, f y ∂ν) = ∫ y, w y*f y ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul (hw.ennreal_ofReal)
      (Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)) f]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by simp only [ENNReal.toReal_ofReal (hw0 y),smul_eq_mul])
  have hweight (S : Set Y) : (fun y => w y*S.indicator (fun _ => (1:ℝ)) y) = S.indicator w := by
    funext y
    by_cases hy : y ∈ S <;> simp [hy]
  have hν (S : Set Y) (hS : MeasurableSet S) : ν.real S = ∫ y, S.indicator w y ∂μ := by
    calc
      _ = ∫ y, S.indicator (fun _ => (1:ℝ)) y ∂ν := by simp [integral_indicator hS]
      _ = _ := by rw [hchange,hweight]
  let δ := fun y => ENNReal.ofReal (d y)
  have hδ : Measurable δ := hd.ennreal_ofReal
  have hg (s : ℝ) (hs : 0 < s) : ν.real {y | δ y < ENNReal.ofReal s} ≤ C*s^4 := by
    let S := {y | δ y < ENNReal.ofReal s}
    let T := {y | d y ≤ s}
    have hS : MeasurableSet S := measurableSet_lt hδ measurable_const
    have hT : MeasurableSet T := measurableSet_le hd measurable_const
    have hsub : S ⊆ T := by
      intro y hy
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mp hy)
    rw [hν S hS]
    apply (integral_mono (hwi.indicator hS) (hwi.indicator hT) ?_).trans (hgrowth s hs)
    intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy,indicator_of_mem (hsub hy)]
    · rw [indicator_of_notMem hy]
      exact Set.indicator_nonneg (fun z _ => hw0 z) y
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_profile_le ν δ hδ C hC hg hr)
  rw [ENNReal.toReal_ofReal (by positivity),← integral_profile_toReal ν δ hδ,hchange] at hh
  have he (y : Y) : (profile r (δ y)).toReal = ((1+d y/r)⁻¹)^6 := by
    rw [profile_ofReal hr (hd0 y),ENNReal.toReal_ofReal (by positivity)]
  simpa only [he] using hh
end TamingCompatibility.FourthShell

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [CompactSpace X] in
lemma euclideanAngularGlobal_measurable (p : A.centers) : Measurable (euclideanAngularGlobal A J α hs ht E p) := by
  classical
  exact (euclideanAngularWeight_continuousOn A J α hs ht E p).measurable_piecewise continuousOn_const
    (angularDomain_closed A J α hs ht E p).measurableSet

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [CompactSpace X] in
lemma euclideanDistanceGlobal_measurable (p : A.centers) : Measurable (euclideanDistanceGlobal A J α hs ht E p) := by
  classical
  exact ((angularChartCoordinates_continuousOn A J α hs ht E p).snd.sub
    (angularChartCoordinates_continuousOn A J α hs ht E p).fst).norm.measurable_piecewise continuousOn_const
    (angularDomain_closed A J α hs ht E p).measurableSet

include hE hD in
lemma separating_current_euclidean_angular_profile_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        ((1+euclideanDistanceGlobal A J α hs ht E p uv/r)⁻¹)^6 ∂μ.prod μ) ≤ C*r^4 := by
  obtain ⟨F,hF,hgrowth⟩ := separating_current_euclidean_angular_moment A J α hs ht E hE D hD μ hann p
  let w := euclideanAngularGlobal A J α hs ht E p
  let d := euclideanDistanceGlobal A J α hs ht E p
  have hw := euclideanAngularGlobal_measurable A J α hs ht E p
  have hd := euclideanDistanceGlobal_measurable A J α hs ht E p
  have hw0 (uv) : 0 ≤ w uv := Set.indicator_nonneg (fun v _ => euclideanAngularWeight_nonneg A J α hs ht p v) uv
  have hd0 (uv) : 0 ≤ d uv := Set.indicator_nonneg (fun _ _ => norm_nonneg _) uv
  have hwi : Integrable w (μ.prod μ) := by
    refine (integrable_const (4:ℝ)).mono' hw.aestronglyMeasurable (ae_of_all _ fun uv => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (hw0 uv)]
    by_cases huv : uv ∈ angularDomain A J α hs ht E p
    · exact (Set.indicator_of_mem huv _).le.trans (euclideanAngularWeight_le A J α hs ht E p huv)
    · simp only [w,euclideanAngularGlobal,Set.indicator_of_notMem huv] <;> norm_num
  have he (s : ℝ) : {uv | d uv ≤ s}.indicator w = euclideanAngularNear A J α hs ht E s p := by
    funext uv
    by_cases huv : uv ∈ angularDomain A J α hs ht E p
    · simp [d,w,euclideanDistanceGlobal,euclideanAngularGlobal,euclideanAngularNear,euclideanNearSet,Set.indicator,huv]
    · simp [w,euclideanAngularGlobal,euclideanAngularNear,euclideanNearSet,Set.indicator,huv]
  refine ⟨32*F,by positivity,fun r hr => ?_⟩
  exact FourthShell.weighted_profile_bound (μ.prod μ) w d hw hd hw0 hd0 hwi F hF
    (fun s hs' => by rw [he]; exact hgrowth s hs') hr
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile_oai.{u_1}
