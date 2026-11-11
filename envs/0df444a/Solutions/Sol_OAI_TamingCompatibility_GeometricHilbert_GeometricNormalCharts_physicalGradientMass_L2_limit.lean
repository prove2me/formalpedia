-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:47.005864+00:00
-- url     : https://prove2.me/submissions/5dac061d-a388-4b61-8c60-37e827c6fafd

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc020
import Definitions.Def_OAIQ239Tc021
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
lemma scalarChartLift_apply_inverse (p : X) (f : Space → ℝ)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    scalarChartLift p f ((extChartAt Model p).symm z) = f z := by
  classical
  simp only [scalarChartLift,ite_eq_left ((extChartAt Model p).map_target hz),
    (extChartAt Model p).right_inv hz]

omit [IsManifold Model ∞ X] in
lemma scalarChartLift_tsupport (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    tsupport (scalarChartLift p f) ⊆ scalarLiftSupport p f := by
  apply closure_minimal _ (scalarLiftSupport_compact p hc hf).isClosed
  intro x hx
  by_contra h
  exact hx (scalarChartLift_zero_off p f h)

end TamingCompatibility.ManifoldForms

end
end

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
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_GeometricSeparatingProbability
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RiemannianChartPowerMass
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set _root_.MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem local_chart_mass_power_to_riemannian {Y : Type*} [MeasurableSpace Y]
    (proj : Y → X) (μ : Measure Y) [IsFiniteMeasure μ] (n : ℕ)
    (hloc : ∀ x : X, ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : Y | proj u ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^n := by
  let : EMetricSpace X := .ofRiemannianMetric Model X
  let P := fun (x : X) (C : ℝ) => ∀ s : ℝ, 0 < s →
    μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^n
  suffices hlocal : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C by
    obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound (isCompact_univ : IsCompact (univ : Set X))
      P (fun _ a b hab ha s hs => (ha s hs).trans
        (mul_le_mul_of_nonneg_right hab (pow_nonneg hs.le n))) hlocal
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
  have hCL : 0 ≤ C*(L:ℝ)^n := mul_nonneg hC (pow_nonneg L.coe_nonneg n)
  let D : ℝ := C*(L:ℝ)^n + μ.real univ/q^n
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
      _ ≤ C*((L:ℝ)*s)^n := hmass _ ⟨mul_pos hLp hs,hsLr⟩ _ (Metric.ball_subset_closedBall hy.2)
      _ = (C*(L:ℝ)^n)*s^n := by rw [mul_pow,mul_assoc]
      _ ≤ D*s^n := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (pow_nonneg hs.le n)
  · have hqs : q ≤ s := le_of_lt (lt_of_not_ge hsq)
    have hpow : q^n ≤ s^n := pow_le_pow_left₀ hq.le hqs n
    have hlarge : μ.real univ ≤ (μ.real univ/q^n)*s^n := by
      rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hq n)]
      exact mul_le_mul_of_nonneg_left hpow (measureReal_nonneg)
    exact (measureReal_mono (subset_univ _)).trans (hlarge.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) (pow_nonneg hs.le n)))
end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_BoundedMassLimit
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory Filter Set
open scoped Topology
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma tendstoInMeasure_of_integral_nonneg {ι : Type*} {l : Filter ι}
    (f : ι → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (hp : ∀ n, 0 ≤ᵐ[μ] f n)
    (hl : Tendsto (fun n => ∫ x, f n x ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (hf := fun _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (p := 1) one_ne_zero
  have he (n : ι) : eLpNorm (f n - (fun _ => 0)) 1 μ = ENNReal.ofReal (∫ x, f n x ∂μ) := by
    simp only [eLpNorm_one_eq_lintegral_enorm,Pi.sub_apply,sub_zero]
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf n)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hp n] with x hx
    exact Real.norm_of_nonneg hx
  simpa only [he,ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl

lemma integral_weight_mul_tendsto_zero_of_inMeasure
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ) (hp : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C)
    (hl : TendstoInMeasure μ f l (fun _ => 0))
    (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms,_,hms⟩ := (hl.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g x*f (ns (ms n)) x) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hms] with x hx
    simpa only [Function.comp_apply,mul_zero] using tendsto_const_nhds.mul hx
  have hh := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖*C)
    (fun n => hg.aestronglyMeasurable.mul (hf _)) (hg.norm.mul_const C)
    (fun n => (hp (ns (ms n))).mono (fun x hx => by
      rw [Pi.mul_apply,norm_mul]
      exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))) hlim
  simpa only [integral_zero,Pi.mul_apply] using hh

lemma integral_weight_mul_tendsto_zero_of_bounded_mass
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (C : ℝ) (hp : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x ∧ f n x ≤ C)
    (hl : Tendsto (fun n => ∫ x, f n x ∂μ) l (𝓝 0))
    (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 0) := by
  apply integral_weight_mul_tendsto_zero_of_inMeasure f (fun n => (hf n).aestronglyMeasurable) C
  · intro n
    filter_upwards [hp n] with x hx
    simpa only [Real.norm_of_nonneg hx.1] using hx.2
  · exact tendstoInMeasure_of_integral_nonneg f hf (fun n => (hp n).mono fun _ h => h.1) hl
  · exact hg
end TamingCompatibility

end
end

section

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sqrt_memLp_two (f : Ω → ℝ) (hi : Integrable f μ) (hp : ∀ x, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  rw [memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)]
  simpa only [Real.sq_sqrt (hp _)] using hi

lemma integral_sqrt_mul_sqrt_le (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x) :
    (∫ x, Real.sqrt (f x)*Real.sqrt (g x) ∂μ) ≤
      Real.sqrt (∫ x, f x ∂μ)*Real.sqrt (∫ x, g x ∂μ) := by
  have hf' := sqrt_memLp_two f hf hfp
  have hg' := sqrt_memLp_two g hg hgp
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => Real.sqrt_nonneg (f x)) (ae_of_all μ fun x => Real.sqrt_nonneg (g x))
    (show MemLp (fun x => Real.sqrt (f x)) (ENNReal.ofReal (2:ℝ)) μ by simpa using hf')
    (show MemLp (fun x => Real.sqrt (g x)) (ENNReal.ofReal (2:ℝ)) μ by simpa using hg')
  simp only [Real.rpow_two,Real.sq_sqrt (hfp _),Real.sq_sqrt (hgp _)] at hh
  simpa only [Real.sqrt_eq_rpow,one_div] using hh

end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_SchurVanishing
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] {μ : Measure Ω}

lemma integral_norm_mul_tendsto_of_schur
    (q : Ω → V) (hq : MemLp q 2 μ)
    (H : ℝ → Ω → ℝ) (hH : ∀ r, 0 < r → Integrable (H r) μ)
    (hH0 : ∀ r x, 0 ≤ H r x) (C D : ℝ) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbound : ∀ r, 0 < r → ∀ x, r*H r x ≤ C)
    (hmass : ∀ r, 0 < r → (∫ x, H r x ∂μ) ≤ D*r) :
    Tendsto (fun r : ℝ => ∫ x, ‖q x‖*H r x ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  classical
  let F := fun (r : ℝ) (x : Ω) => if 0 < r then r*H r x else 0
  have hFi (r : ℝ) : Integrable (F r) μ := by
    by_cases hr : 0 < r
    · simpa only [F,ite_eq_left hr] using (hH r hr).const_mul r
    · simp only [F,ite_eq_right hr]; exact integrable_zero _ _ _
  have hFp (r : ℝ) (x : Ω) : 0 ≤ F r x ∧ F r x ≤ C := by
    by_cases hr : 0 < r
    · simp only [F,ite_eq_left hr]
      exact ⟨mul_nonneg hr.le (hH0 r x),hbound r hr x⟩
    · simp only [F,ite_eq_right hr]
      exact ⟨le_rfl,hC⟩
  have hFl : Tendsto (fun r => ∫ x, F r x ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun x => (hFp r x).1)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r at hr
      simp only [F,ite_eq_left hr,integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (hmass r hr) hr.le).trans_eq (by ring : r*(D*r) = D*r^2)
    · have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero] using (tendsto_const_nhds (x := D)).mul (hid.pow 2)
  have hq2 : Integrable (fun x => ‖q x‖^2) μ := hq.norm.integrable_sq
  have hweighted := integral_weight_mul_tendsto_zero_of_bounded_mass F hFi C
    (fun r => ae_of_all _ (hFp r)) hFl (fun x => ‖q x‖^2) hq2
  have hlim : Tendsto (fun r => Real.sqrt (∫ x, ‖q x‖^2*F r x ∂μ)*Real.sqrt D)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_mul,Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0 |>.comp hweighted).mul tendsto_const_nhds
  apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun x => mul_nonneg (norm_nonneg _) (hH0 r x))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    have hfi : Integrable (fun x => ‖q x‖^2*(r*H r x)) μ := by
      apply (hq2.mul_const C).mono' (hq2.aestronglyMeasurable.mul ((hH r hr).aestronglyMeasurable.const_mul r))
      apply ae_of_all
      intro x
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hr.le (hH0 r x)))]
      exact mul_le_mul_of_nonneg_left (hbound r hr x) (sq_nonneg _)
    have hgi : Integrable (fun x => H r x/r) μ := (hH r hr).div_const r
    have hfpos (x : Ω) : 0 ≤ ‖q x‖^2*(r*H r x) := mul_nonneg (sq_nonneg _) (mul_nonneg hr.le (hH0 r x))
    have hgpos (x : Ω) : 0 ≤ H r x/r := div_nonneg (hH0 r x) hr.le
    have he (x : Ω) : ‖q x‖*H r x =
        Real.sqrt (‖q x‖^2*(r*H r x))*Real.sqrt (H r x/r) := by
      rw [← Real.sqrt_mul (hfpos x)]
      have ha : ‖q x‖^2*(r*H r x)*(H r x/r) = (‖q x‖*H r x)^2 := by field_simp [hr.ne']
      rw [ha,Real.sqrt_sq (mul_nonneg (norm_nonneg _) (hH0 r x))]
    calc
      _ = ∫ x, Real.sqrt (‖q x‖^2*(r*H r x))*Real.sqrt (H r x/r) ∂μ := integral_congr_ae (ae_of_all _ he)
      _ ≤ Real.sqrt (∫ x, ‖q x‖^2*(r*H r x) ∂μ)*Real.sqrt (∫ x, H r x/r ∂μ) :=
        integral_sqrt_mul_sqrt_le _ _ hfi hgi hfpos hgpos
      _ ≤ Real.sqrt (∫ x, ‖q x‖^2*F r x ∂μ)*Real.sqrt D := by
        simp only [F,ite_eq_left hr]
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (Real.sqrt_nonneg _)
        rw [integral_div]
        exact (div_le_iff₀ hr).mpr (hmass r hr)
  · exact hlim
end TamingCompatibility

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
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldPairingInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] in
lemma chart_density_compact_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ L, chartDensity J α p z ≤ C := by
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn ((chartDensity_smooth J α hs ht p).continuousOn.mono hLt)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (le_abs_self _).trans ((hC z hz).trans (le_max_left _ _))⟩

include hs ht in

lemma integral_chart_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (D : ℝ) (hD : 0 ≤ D)
    (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfs : Function.support f ⊆ (extChartAt Model p).symm '' L)
    (G : Space → ℝ) (hGi : Integrable G) (hG0 : ∀ z, 0 ≤ G z)
    (hGf : ∀ z ∈ (extChartAt Model p).target, f ((extChartAt Model p).symm z) ≤ G z) :
    (∫ x, f x ∂geometricVolume A J α) ≤ D*(∫ z, G z) := by
  have hLc : IsCompact ((extChartAt Model p).symm '' L) :=
    hL.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hLt)
  have hts : tsupport f ⊆ (extChartAt Model p).symm '' L := closure_minimal hfs hLc.isClosed
  have hts' : tsupport f ⊆ (extChartAt Model p).source := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hts hx
    exact (extChartAt Model p).map_target (hLt hz)
  have hcgi := coordinateIntegrand_integrable J α hs ht p f hf hts'
  have hpoint (z : Space) : coordinateIntegrand J α p f z ≤ D*G z := by
    by_cases hzt : z ∈ (extChartAt Model p).target
    · rw [coordinateIntegrand,Set.indicator_of_mem hzt]
      by_cases hz : z ∈ L
      · exact mul_le_mul (hDb z hz) (hGf z hzt) (hf0 _) hD
      · have hfz : f ((extChartAt Model p).symm z) = 0 := by
          apply Function.notMem_support.mp
          intro hh
          obtain ⟨w,hw,he⟩ := hfs hh
          have he' := congrArg (extChartAt Model p) he
          rw [(extChartAt Model p).right_inv (hLt hw),(extChartAt Model p).right_inv hzt] at he'
          exact hz (he' ▸ hw)
        rw [hfz,mul_zero]
        exact mul_nonneg hD (hG0 z)
    · rw [coordinateIntegrand,Set.indicator_of_notMem hzt]
      exact mul_nonneg hD (hG0 z)
  rw [integral_geometricVolume_coordinate A J α hs ht p f hf hts',
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  change (∫ z, coordinateIntegrand J α p f z) ≤ _
  calc
    _ ≤ ∫ z, D*G z := integral_mono hcgi (hGi.const_mul D) hpoint
    _ = _ := integral_const_mul _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricVolumeGrowth
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
lemma volume_chart_closedBall_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (D : ℝ) (hD : 0 ≤ D)
    (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (b : Space) {s : ℝ} (hs0 : 0 < s) (hsub : Metric.closedBall b (2*s) ⊆ L) :
    (geometricVolume A J α).real ((extChartAt Model p).symm '' Metric.closedBall b s) ≤
      D*((2*s)^4*volume.real (Metric.closedBall (0:Space) 1)) := by
  classical
  let := geometricVolume_finite A J α hs ht
  let φ : ContDiffBump b := ⟨s,2*s,hs0,by linarith⟩
  have hφt : tsupport (φ : Space → ℝ) ⊆ (extChartAt Model p).target := by
    rw [φ.tsupport_eq]
    exact hsub.trans hLt
  let f : X → ℝ := scalarChartLift p φ
  have hf : Continuous f := (scalarChartLift_smooth p φ.contDiff φ.hasCompactSupport hφt).continuous
  have hf0 (x : X) : 0 ≤ f x := by
    by_cases hx : x ∈ (extChartAt Model p).source
    · simpa only [f,scalarChartLift,ite_eq_left hx] using φ.nonneg (x := extChartAt Model p x)
    · simp only [f,scalarChartLift,ite_eq_right hx,le_refl]
  have hfs : Function.support f ⊆ (extChartAt Model p).symm '' L := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := scalarChartLift_tsupport p φ.hasCompactSupport hφt (subset_tsupport f hx)
    exact ⟨z,hsub (by simpa only [φ.tsupport_eq] using hz),rfl⟩
  let G : Space → ℝ := (Metric.closedBall b (2*s)).indicator (fun _ => 1)
  have hGi : Integrable G := by
    exact (integrableOn_const (C := (1:ℝ))
      (hs := (isCompact_closedBall b (2*s)).measure_lt_top.ne)).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
  have hG0 (z : Space) : 0 ≤ G z := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
  have hGf (z : Space) (hz : z ∈ (extChartAt Model p).target) : f ((extChartAt Model p).symm z) ≤ G z := by
    rw [show f ((extChartAt Model p).symm z) = φ z from scalarChartLift_apply_inverse p φ hz]
    by_cases hzb : z ∈ Metric.closedBall b (2*s)
    · simpa only [G,Set.indicator_of_mem hzb] using φ.le_one (x := z)
    · have hzφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (by
        simpa only [φ.tsupport_eq] using hzb)
      simp only [G,Set.indicator_of_notMem hzb,hzφ,le_refl]
  have hub := integral_chart_bound J α hs ht A p L hL hLt D hD hDb f hf hf0 hfs G hGi hG0 hGf
  have hst : Metric.closedBall b s ⊆ (extChartAt Model p).target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans (hsub.trans hLt)
  have hK : IsCompact ((extChartAt Model p).symm '' Metric.closedBall b s) :=
    (isCompact_closedBall b s).image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hst)
  have hli : Integrable (((extChartAt Model p).symm '' Metric.closedBall b s).indicator (fun _ => (1:ℝ)))
      (geometricVolume A J α) := (integrable_const (1:ℝ)).indicator hK.measurableSet
  have hfi : Integrable f (geometricVolume A J α) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hlb : (geometricVolume A J α).real ((extChartAt Model p).symm '' Metric.closedBall b s) ≤
      ∫ x, f x ∂geometricVolume A J α := by
    rw [← integral_indicator_one hK.measurableSet]
    apply integral_mono hli hfi
    intro x
    by_cases hx : x ∈ (extChartAt Model p).symm '' Metric.closedBall b s
    · rw [Set.indicator_of_mem hx]
      obtain ⟨z,hz,rfl⟩ := hx
      rw [show f ((extChartAt Model p).symm z) = φ z from scalarChartLift_apply_inverse p φ (hst hz)]
      exact (φ.one_of_mem_closedBall hz).ge
    · rw [Set.indicator_of_notMem hx]
      exact hf0 x
  have hG : (∫ z, G z) = (2*s)^4*volume.real (Metric.closedBall (0:Space) 1) := by
    change (∫ z, (Metric.closedBall b (2*s)).indicator (1 : Space → ℝ) z) = _
    rw [integral_indicator_one Metric.isClosed_closedBall.measurableSet,
      Measure.addHaar_real_closedBall' volume b (by positivity)]
    congr 1
    simp [Space]
  exact hlb.trans (by simpa only [hG] using hub)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricQuadraticMass
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricVolumeBall
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms ManifoldVolume ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
lemma geometricVolume_chart_power_growth (x : X) :
    ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        (geometricVolume A J α).real ((extChartAt Model p).symm '' Metric.closedBall b s) ≤ C*s^4 := by
  have hx := mem_extChartAt_target (I := Model) x
  obtain ⟨δ,hδ,hδt⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := Model) x) _ hx
  let R := δ/8
  have hR : 0 < R := by dsimp [R] <;> positivity
  have h4 : Metric.closedBall (extChartAt Model x x) (4*R) ⊆ (extChartAt Model x).target := by
    apply Set.Subset.trans _ hδt
    exact Metric.closedBall_subset_ball (by dsimp [R] <;> linarith)
  obtain ⟨D,hD,hDb⟩ := chart_density_compact_bound J α hs ht x
    (Metric.closedBall (extChartAt Model x x) (4*R)) (isCompact_closedBall _ _) h4
  refine ⟨x,R,D*2^4*volume.real (Metric.closedBall (0:Space) 1),R,mem_extChartAt_source (I := Model) x,
    hR,by positivity,hR,h4,?_⟩
  intro s hs0 b hb
  have hsub : Metric.closedBall b (2*s) ⊆ Metric.closedBall (extChartAt Model x x) (4*R) := by
    intro z hz
    have htri := dist_triangle z b (extChartAt Model x x)
    change dist z (extChartAt Model x x) ≤ 4*R
    change dist z b ≤ 2*s at hz
    change dist b (extChartAt Model x x) ≤ R at hb
    linarith [hs0.2]
  have h := volume_chart_closedBall_bound J α hs ht A x
    (Metric.closedBall (extChartAt Model x x) (4*R)) (isCompact_closedBall _ _) h4
    D hD hDb b hs0.1 hsub
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma geometricVolume_hermitian_ball_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      (geometricVolume A J α).real {y | hermitianEDist J α hs ht x y < ENNReal.ofReal s} ≤ C*s^4 := by
  let := geometricVolume_finite A J α hs ht
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  exact local_chart_mass_power_to_riemannian (fun x : X => x) (geometricVolume A J α) 4
    (geometricVolume_chart_power_growth J α hs ht A)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianShell
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
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

omit [MeasurableSpace X] [BorelSpace X] in
lemma hermitianEDist_continuous (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) :
    Continuous (fun p : X×X => hermitianEDist J α hs ht p.1 p.2) := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let : EMetricSpace X := .ofRiemannianMetric Model X
  exact continuous_fst.edist continuous_snd

omit [MeasurableSpace X] [BorelSpace X] in
lemma hermitianEDist_unit_measurable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x : X) :
    Measurable (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      hermitianEDist J α hs ht x u.val.proj) := by
  have hp := (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp
    (continuous_subtype_val : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val))
  exact ((hermitianEDist_continuous J α hs ht).comp (continuous_const.prodMk hp)).measurable

end TamingCompatibility

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma hermitianEDist_ne_top (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) :
    hermitianEDist J α hs ht x y ≠ ⊤ := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let : EMetricSpace X := .ofRiemannianMetric Model X
  change edist x y ≠ ⊤
  have hb : Metric.eball x ⊤ = univ :=
    (show IsClopen (Metric.eball x ⊤) from
      ⟨Metric.isClosed_eball_top,Metric.isOpen_eball⟩).eq_univ
      ⟨x,by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hb]; trivial
  exact (by simpa only [Metric.mem_eball,edist_comm] using hy : edist x y < ⊤).ne

lemma hermitian_profile_toReal (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) {r : ℝ} (hr : 0 < r) :
    (QuadraticShell.profile r (hermitianEDist J α hs ht x y)).toReal =
      (1+(hermitianEDist J α hs ht x y).toReal/r)⁻¹^6 := by
  have hd := hermitianEDist_ne_top J α hs ht x y
  conv_lhs => rw [← ENNReal.ofReal_toReal hd, QuadraticShell.profile_ofReal hr ENNReal.toReal_nonneg]
  rw [ENNReal.toReal_ofReal (by positivity)]

end TamingCompatibility

end
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianShellIntegral
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
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set _root_.MeasureTheory Filter
open scoped Bundle Manifold ContDiff ENNReal Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem separating_probability_real_shell
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r →
      (∫ u, (1+(hermitianEDist J α hs ht x u.val.proj).toReal/r)⁻¹^6 ∂μ)/r^2 ≤ C := by
  obtain ⟨C,hC,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  refine ⟨8*C,by positivity,fun x r hr => ?_⟩
  have h := QuadraticShell.integral_profile_normalized_bound μ _
    (hermitianEDist_unit_measurable J α hs ht x) C hC (hgrowth x) hr
  simpa only [hermitian_profile_toReal J α hs ht _ _ hr] using h

end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PhysicalProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (fun xy : X×X => physicalProfile J α hs ht r xy.1 xy.2) := by
  let := geometricMetricSpace J α hs ht
  change Continuous (fun xy : X×X => ((1+dist xy.1 xy.2/r)⁻¹)^6)
  exact ((continuous_const.add ((continuous_fst.dist continuous_snd).div_const r)).inv₀
    (fun xy => (show 0 < 1+dist xy.1 xy.2/r by positivity).ne')).pow 6

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfile_nonneg (r : ℝ) (x y : X) : 0 ≤ physicalProfile J α hs ht r x y := by
  unfold physicalProfile
  positivity

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_symm (r : ℝ) (x y : X) : physicalProfile J α hs ht r x y = physicalProfile J α hs ht r y x := by
  let := geometricMetricSpace J α hs ht
  change ((1+dist x y/r)⁻¹)^6 = ((1+dist y x/r)⁻¹)^6
  rw [dist_comm]

omit [SecondCountableTopology X] in
lemma physicalProfile_volume_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : X, ∀ r : ℝ, 0 < r →
      (∫ x, physicalProfile J α hs ht r x y ∂geometricVolume A J α) ≤ C*r^4 := by
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hgrowth⟩ := geometricVolume_hermitian_ball_growth J α hs ht A
  refine ⟨32*C,by positivity,fun y r hr => ?_⟩
  have hδ : Measurable (fun x => hermitianEDist J α hs ht y x) :=
    ((hermitianEDist_continuous J α hs ht).comp (continuous_const.prodMk continuous_id)).measurable
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (FourthShell.lintegral_profile_le (geometricVolume A J α) _ hδ C hC (hgrowth y) hr)
  rw [ENNReal.toReal_ofReal (by positivity),← QuadraticShell.integral_profile_toReal _ _ hδ] at hh
  simp_rw [hermitian_profile_toReal J α hs ht _ _ hr] at hh
  change (∫ x, physicalProfile J α hs ht r y x ∂geometricVolume A J α) ≤ _ at hh
  simpa only [physicalProfile_symm J α hs ht r y] using hh

lemma physicalProfile_unit_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable
      (fun xu : X × MetricUnit (hermitianMetric J α hs ht) => physicalProfile J α hs ht r xu.1 xu.2.val.proj)
      ((geometricVolume A J α).prod μ) := by
  let := geometricVolume_finite A J α hs ht
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hmap : Continuous (fun xu : X × MetricUnit (hermitianMetric J α hs ht) => (xu.1,xu.2.val.proj)) :=
    continuous_fst.prodMk (hp.comp continuous_snd)
  have hh := (physicalProfile_continuous J α hs ht hr).comp hmap
  exact hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma physicalProfileMass_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (physicalProfileMass J α hs ht μ r) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (physicalProfile_unit_integrable A J α hs ht μ hr).integral_prod_left

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfileMass_nonneg
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) (x : X) :
    0 ≤ physicalProfileMass J α hs ht μ r x :=
  integral_nonneg (fun u => physicalProfile_nonneg J α hs ht r x u.val.proj)

lemma physicalProfileMass_volume_growth
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ x, physicalProfileMass J α hs ht μ r x ∂geometricVolume A J α) ≤ C*r^4 := by
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hgrowth⟩ := physicalProfile_volume_growth A J α hs ht
  refine ⟨C,hC,fun r hr => ?_⟩
  unfold physicalProfileMass
  rw [integral_integral_swap (physicalProfile_unit_integrable A J α hs ht μ hr)]
  have hi := (physicalProfile_unit_integrable A J α hs ht μ hr).integral_prod_right
  have hh := integral_mono hi (integrable_const (C*r^4)) (fun u => hgrowth u.val.proj r hr)
  simpa only [integral_const,probReal_univ,one_smul] using hh
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PhysicalSchur
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] in
lemma physicalProfileMass_quadratic
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r →
      physicalProfileMass J α hs ht μ r x ≤ C*r^2 := by
  obtain ⟨C,hC,hbound⟩ := separating_probability_real_shell J α hs ht μ hann
  refine ⟨C,hC,fun x r hr => ?_⟩
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mp (hbound x r hr)

lemma physicalGradientMass_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    Integrable (physicalGradientMass J α hs ht μ L r) (geometricVolume A J α) :=
  (physicalProfileMass_integrable A J α hs ht μ (mul_pos hL hr)).div_const (r^3)

lemma physicalGradientMass_schur
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) {L : ℝ} (hL : 0 < L) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ r : ℝ, 0 < r →
      (∀ x, r*physicalGradientMass J α hs ht μ L r x ≤ C) ∧
      (∫ x, physicalGradientMass J α hs ht μ L r x ∂geometricVolume A J α) ≤ D*r := by
  obtain ⟨C,hC,hbound⟩ := physicalProfileMass_quadratic J α hs ht μ hann
  obtain ⟨D,hD,hvolume⟩ := physicalProfileMass_volume_growth A J α hs ht μ
  refine ⟨C*L^2,D*L^4,by positivity,by positivity,fun r hr => ⟨?_,?_⟩⟩
  · intro x
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hbound x (L*r) (mul_pos hL hr)) (by positivity : 0 ≤ r^3)) hr.le
    have he : r*(C*(L*r)^2/r^3) = C*L^2 := by field_simp
    exact hh.trans_eq he
  · unfold physicalGradientMass
    rw [integral_div]
    calc
      _ ≤ D*(L*r)^4/r^3 := div_le_div_of_nonneg_right (hvolume (L*r) (mul_pos hL hr)) (by positivity)
      _ = _ := by field_simp

lemma physicalGradientMass_L2_limit_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    {V : Type*} [NormedAddCommGroup V] (q : X → V) (hq : MemLp q 2 (geometricVolume A J α))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun r : ℝ => ∫ x, ‖q x‖*physicalGradientMass J α hs ht μ L r x ∂geometricVolume A J α)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := physicalGradientMass_schur A J α hs ht μ hann hL

  let H := fun r x => if 0 < r then physicalGradientMass J α hs ht μ L r x else 0
  have hi (r : ℝ) (hr : 0 < r) : Integrable (H r) (geometricVolume A J α) := by
    simpa only [H,ite_eq_left hr] using physicalGradientMass_integrable A J α hs ht μ hL hr
  have hn (r : ℝ) (x : X) : 0 ≤ H r x := by
    by_cases hr : 0 < r
    · simp only [H,ite_eq_left hr,physicalGradientMass]
      exact div_nonneg (physicalProfileMass_nonneg J α hs ht μ _ _) (by positivity)
    · simp only [H,ite_eq_right hr,le_refl]
  have hh := integral_norm_mul_tendsto_of_schur q hq H hi hn C D hC hD
    (fun r hr x => by simpa only [H,ite_eq_left hr] using (hbound r hr).1 x)
    (fun r hr => by simpa only [H,ite_eq_left hr] using (hbound r hr).2)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [H,ite_eq_left (show 0 < r from hr)]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit_oai.{u_1, u_2} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit_oai.{u_1, u_2}
