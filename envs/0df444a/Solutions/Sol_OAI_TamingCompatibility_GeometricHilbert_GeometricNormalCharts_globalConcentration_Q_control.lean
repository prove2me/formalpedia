-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:43.915783+00:00
-- url     : https://prove2.me/submissions/31e31ac9-19c9-4e3a-a04e-af4960667db3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc020
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_physicalGradientMass_L2_limit

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldScalarCalculus
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_sum {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, MDifferentiable Model 𝓘(ℝ,ℝ) (f i)) :
    scalarDifferential (∑ i ∈ s, f i) = ∑ i ∈ s, scalarDifferential (f i) := by
  funext x
  have hh : HasMFDerivAt Model 𝓘(ℝ,ℝ) (∑ i ∈ s, f i) x
      (∑ i ∈ s, (show Space →L[ℝ] ℝ from mfderiv Model 𝓘(ℝ,ℝ) (f i) x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using! (hasMFDerivAt_const (I := Model) (I' := 𝓘(ℝ,ℝ)) (0 : ℝ) x)
    | insert i s hi IH =>
      erw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact ((hf i (Finset.mem_insert_self i s) x).hasMFDerivAt).add
        (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
  unfold scalarDifferential
  rw [hh.mfderiv]
  change (ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1))
    (∑ i ∈ s, mfderiv Model 𝓘(ℝ,ℝ) (f i) x) = _
  erw [_root_.map_sum]
  change ∑ i ∈ s, scalarDifferential (f i) x = (∑ i ∈ s, scalarDifferential (f i)) x
  exact (Finset.sum_apply x s (fun i => scalarDifferential (f i))).symm

omit [IsManifold Model ∞ X] in
lemma wedgeOne_sum_left {ι : Type*} (s : Finset ι) (a : ι → Form X 1) (b : Form X 1) :
    wedgeOne (∑ i ∈ s, a i) b = ∑ i ∈ s, wedgeOne (a i) b := by
  funext x
  simp only [wedgeOne,Finset.sum_apply, ExteriorForms.oneLinear]
  erw [_root_.map_sum]
  exact _root_.map_sum (ExteriorForms.wedgeOneRight (E := Space) (b x)) _ _

end TamingCompatibility.ManifoldForms

end
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

omit [IsManifold Model ∞ X] [T2Space X] in

lemma scalarChartLift_fderiv (p : X) (f : Space → ℝ) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    fderiv ℝ (scalarChartLift p f ∘ (extChartAt Model p).symm) z = fderiv ℝ f z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  exact scalarChartLift_apply_inverse p f hw

end TamingCompatibility.ManifoldForms

end
end

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
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_nonneg (r : ℝ) (z : V) : 0 ≤ rationalKernel r z := by
  unfold rationalKernel
  positivity

lemma rationalKernel_deriv {r : ℝ} (hr : 0 < r) (z v : V) :
    fderiv ℝ (rationalKernel r) z v =
      -(6*r^4/(r^2+‖z‖^2)^4)*⟪z,v⟫ := by
  have hd : r^2+‖z‖^2 ≠ 0 := ne_of_gt (by positivity)
  have hh₀ := (hasDerivAt_const (‖z‖^2) (r^4)).div
    (((hasDerivAt_id (‖z‖^2)).const_add (r^2)).pow 3) (pow_ne_zero _ hd)
  have hh := hh₀.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  change HasFDerivAt (rationalKernel r) _ z at hh
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, Pi.pow_apply, id_eq, innerSL_apply_apply]
  field_simp
  ring

omit [InnerProductSpace ℝ V] in
lemma compact_continuous_bound {W : Type*} [NormedAddCommGroup W]
    (f : V → W) (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C := by
  obtain ⟨C,hC⟩ := hs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz,norm_zero]
    exact le_max_right _ _

section Measure
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma hasFDerivAt_finite_convolution (μ : Measure V) [IsFiniteMeasure μ]
    (k : V → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (x : V) :
    HasFDerivAt (fun x => ∫ y, k (x-y) ∂μ)
      (∫ y, fderiv ℝ k (x-y) ∂μ) x := by
  have hd : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨C,_,hC⟩ := compact_continuous_bound k hk.continuous hc
  obtain ⟨D,_,hD⟩ := compact_continuous_bound (fderiv ℝ k) hd (hc.fderiv ℝ)
  have hm (a : V) : Continuous (fun y => k (a-y)) := hk.continuous.comp (continuous_const.sub continuous_id)
  have hdm (a : V) : Continuous (fun y => fderiv ℝ k (a-y)) := hd.comp (continuous_const.sub continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := fun _ => D)
    (Filter.univ_mem) (Eventually.of_forall (fun a => (hm a).aestronglyMeasurable))
    ((integrable_const C).mono' (hm x).aestronglyMeasurable (Eventually.of_forall (fun y => hC (x-y))))
    (hdm x).aestronglyMeasurable (Eventually.of_forall (fun y a _ => hD (a-y)))
    (integrable_const D)
  apply Eventually.of_forall
  intro y a _
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id,id_eq] using ((hk.differentiable (by simp)).differentiableAt (x := a-y)).hasFDerivAt.comp a
    ((hasFDerivAt_id a).sub_const y)

lemma finite_convolution_deriv (μ : Measure V) [IsFiniteMeasure μ]
    (k : V → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (x v : V) :
    fderiv ℝ (fun x => ∫ y, k (x-y) ∂μ) x v = ∫ y, fderiv ℝ k (x-y) v ∂μ := by
  rw [(hasFDerivAt_finite_convolution μ k hk hc x).fderiv]
  apply ContinuousLinearMap.integral_apply
  have hd : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  obtain ⟨D,_,hD⟩ := compact_continuous_bound (fderiv ℝ k) hd (hc.fderiv ℝ)
  exact (integrable_const D).mono'
    (hd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (fun y => hD (x-y)))

end Measure

lemma cutKernel_deriv {r : ℝ} (hr : 0 < r) (η : V → ℝ) (hη : ContDiff ℝ ∞ η) (z v : V) :
    fderiv ℝ (cutKernel η r) z v =
      (fderiv ℝ η z v)*rationalKernel r z -
        η z*(6*r^4/(r^2+‖z‖^2)^4)*⟪z,v⟫ := by
  have h₁ := ((hη.differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
  have h₂ := (((rationalKernel_smooth hr).differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
  change fderiv ℝ (η * rationalKernel r) z v = _
  rw [(h₁.mul h₂).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    rationalKernel_deriv hr]
  ring
end TamingCompatibility.Concentration

end
end

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration

lemma radialCoefficient_nonneg (r t : ℝ) : 0 ≤ radialCoefficient r t := by
  unfold radialCoefficient
  positivity

end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma cutKernel_nonneg (η : V → ℝ) (hη : ∀ z, 0 ≤ η z) (r : ℝ) (z : V) :
    0 ≤ cutKernel η r z := mul_nonneg (hη z) (rationalKernel_nonneg r z)

omit [InnerProductSpace ℝ V] in
lemma cutKernel_le (η : V → ℝ) (hη : ∀ z, η z ≤ 1) (r : ℝ) (z : V) :
    cutKernel η r z ≤ rationalKernel r z := mul_le_of_le_one_left (rationalKernel_nonneg r z) (hη z)

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_away {r a : ℝ} (ha : 0 < a) {z : V} (hz : a ≤ ‖z‖) :
    rationalKernel r z ≤ r^4/a^6 := by
  unfold rationalKernel
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hh : a^2 ≤ r^2+‖z‖^2 := by nlinarith [sq_nonneg r,norm_nonneg z]
  have hp := pow_le_pow_left₀ (sq_nonneg a) hh 3
  simpa only [←pow_mul] using hp

lemma bump_derivative_away_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {a : ℝ} (ha : 0 < a)
    (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ z w : V,
      |fderiv ℝ η z w*rationalKernel r z| ≤ C*r^4*‖w‖ := by
  obtain ⟨B,hB,hbound⟩ := compact_continuous_bound (fderiv ℝ η)
    (hη.continuous_fderiv (by simp)) (hηc.fderiv ℝ)
  refine ⟨B/a^6,by positivity,fun r z w => ?_⟩
  by_cases hz : ‖z‖ < a
  · have he : η =ᶠ[𝓝 z] (fun _ => 1) := by
      filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (gt_mem_nhds hz)] with y hy
      exact hηone y hy
    rw [he.fderiv_eq]
    simp only [fderiv_fun_const]
    change |(0 : ℝ)*rationalKernel r z| ≤ _
    rw [zero_mul,abs_zero]
    positivity
  · have hder : |fderiv ℝ η z w| ≤ B*‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ w).trans (mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _))
    rw [abs_mul,abs_of_nonneg (rationalKernel_nonneg r z)]
    calc
      _ ≤ (B*‖w‖)*(r^4/a^6) := mul_le_mul hder (rationalKernel_away ha (le_of_not_gt hz))
        (rationalKernel_nonneg r z) (by positivity)
      _ = _ := by ring

lemma cutKernel_deriv_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ z w : V,
      |fderiv ℝ (cutKernel η r) z w| ≤
        6*radialCoefficient r ‖z‖*|inner ℝ z w| + C*r^4*‖w‖ := by
  obtain ⟨C,hC,hbound⟩ := bump_derivative_away_bound η hη hηc ha hηone
  refine ⟨C,hC,fun r hr z w => ?_⟩
  rw [cutKernel_deriv hr η hη]
  have he : 6*r^4/(r^2+‖z‖^2)^4 = 6*radialCoefficient r ‖z‖ := by unfold radialCoefficient; ring
  rw [he]
  have hp : 0 ≤ 6*radialCoefficient r ‖z‖ := mul_nonneg (by norm_num) (radialCoefficient_nonneg _ _)
  have hm : |η z*(6*radialCoefficient r ‖z‖)*inner ℝ z w| ≤
      6*radialCoefficient r ‖z‖*|inner ℝ z w| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (hη0 z),abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hp (hη1 z)) (abs_nonneg _)
  exact (abs_sub _ _).trans (by linarith [hbound r z w])
end TamingCompatibility.Concentration

end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthMomentKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] in
lemma planeBaseCut_measurable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (planeBaseCut J α hs ht p K) := by
  classical
  exact (unitChartBase_continuousOn J α hs ht p hKT).measurable_piecewise continuousOn_const
    (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] in
lemma planeMeasure_integral (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : Space → W) (hf : Continuous f) :
    (∫ y, f y ∂planeMeasure J α hs ht p K μ) =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u • f (unitChartBase J α hs ht p u)) u ∂μ := by
  rw [planeMeasure,integral_map (planeBaseCut_measurable J α hs ht p hK hKT).aemeasurable
    hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun u => ENNReal.ofReal (planeAreaCut J α hs ht p K u)) from
        ENNReal.measurable_ofReal.comp (planeAreaCut_measurable J α hs ht p hK hKT))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  dsimp only
  rw [ENNReal.toReal_ofReal (planeAreaCut_nonneg J α hs ht p K u)]
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · simp only [planeAreaCut,planeBaseCut,indicator_of_mem hu]
  · simp only [planeAreaCut,indicator_of_notMem hu,zero_smul]
end TamingCompatibility.GeometricHilbert.Hermitian

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

namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V]
lemma rationalKernel_profile {r : ℝ} (hr : 0 < r) (z : V) :
    rationalKernel r z ≤ (8/r^2)*((1+‖z‖/r)⁻¹)^6 := by
  have hs : 0 < r^2+‖z‖^2 := by positivity
  have ht : 0 < r+‖z‖ := by positivity
  have he : ((1+‖z‖/r)⁻¹)^6 = r^6/(r+‖z‖)^6 := by field_simp
  rw [he,rationalKernel]
  have he' : (8/r^2)*(r^6/(r+‖z‖)^6) = 8*r^4/(r+‖z‖)^6 := by field_simp
  rw [he']
  apply (div_le_div_iff₀ (pow_pos hs 3) (pow_pos ht 6)).mpr
  have hsq : (r+‖z‖)^2 ≤ 2*(r^2+‖z‖^2) := by nlinarith [sq_nonneg (r-‖z‖)]
  have hh := pow_le_pow_left₀ (sq_nonneg (r+‖z‖)) hsq 3
  have hh' : (r+‖z‖)^6 ≤ 8*(r^2+‖z‖^2)^3 := by nlinarith [hh]
  nlinarith [mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ r^4)]
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneConvolution
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
open Set Filter _root_.MeasureTheory PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma planeConvolution_deriv (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (b w : Space) :
    fderiv ℝ (planeConvolution J α hs ht p K μ k) b w =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u *
          fderiv ℝ k (b-unitChartBase J α hs ht p u) w) u ∂μ := by
  let := planeMeasure_finite J α hs ht p hK hKT μ
  rw [show planeConvolution J α hs ht p K μ k = (fun b => ∫ y, k (b-y) ∂planeMeasure J α hs ht p K μ) from rfl,
    finite_convolution_deriv _ k hk hc]
  exact planeMeasure_integral J α hs ht p hK hKT μ _
    (((hk.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)).clm_apply continuous_const)

lemma planeWeighted_integrable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : MetricUnit (hermitianMetric J α hs ht) → W)
    (hf : ContinuousOn f (unitChartDomain J α hs ht p K)) :
    Integrable ((unitChartDomain J α hs ht p K).indicator
      (fun u => unitChartArea J α hs ht p u • f u)) μ := by
  have hS := unitChartDomain_closed J α hs ht p hK hKT
  rw [integrable_indicator_iff hS.measurableSet]
  exact ((unitChartArea_continuousOn J α hs ht p hKT).smul hf).integrableOn_compact hS.isCompact

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian NormalMetricCalculus CoordinateOperator
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}

namespace ParametrixData

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_center (D : ParametrixData J α ht p) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) : q ∈ D.concentrationCompact := by
  have hx : (q,0) ∈ D.normalCompact := ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩
  have he : D.normalChart (q,0) = (q,q) := by
    change (q,normalMap D.metricExtension D.frameExtension q 0) = (q,q)
    rw [normalMap_zero]
  exact Or.inl ⟨(q,q),⟨(q,0),hx,he⟩,rfl⟩

end ParametrixData

variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_apply (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) (x : X) : concentrationPatch A J α hs ht E μ p r x =
      A.partition p x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) := by
  by_cases hx : x ∈ (extChartAt Model p.val).source
  · simp only [concentrationPatch,scalarChartLift,ite_eq_left hx,coordinatePartition_apply A p hx]
  · have he : A.partition p x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.subordinate p h))
    simp only [concentrationPatch,scalarChartLift,ite_eq_right hx,he,zero_mul]

omit [T2Space X] [CompactSpace X] in
lemma localConcentration_nonneg (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) (b : Space) : 0 ≤ localConcentration A J α hs ht E μ p r b := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (E p).concentrationCutoff.bump.nonneg (rationalKernel_nonneg _ _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma concentrationDensity_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) {r : ℝ} (hr : 0 < r) (b : Space) :
    Integrable (concentrationDensity A J α hs ht E p r b) μ := by
  exact planeWeighted_integrable J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _
    ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous.comp_continuousOn
      (continuousOn_const.sub (unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target)))

omit [CompactSpace X] in
lemma localConcentration_integral (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) {r : ℝ} (hr : 0 < r) (b : Space) :
    localConcentration A J α hs ht E μ p r b = ∫ u, concentrationDensity A J α hs ht E p r b u ∂μ := by
  exact planeMeasure_integral J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _
    ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous.comp
      (continuous_const.sub continuous_id))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarWedgeBounds
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma one_eval_norm (a : Form (E := V) 1) (v : V) : |a ![v]| ≤ ‖a‖*‖v‖ := by
  have hh := (oneLinear a).le_opNorm v
  rw [oneLinear_apply] at hh
  simpa only [oneLinear,LinearIsometryEquiv.norm_map,Real.norm_eq_abs] using hh

lemma scalar_wedge_norm (l : V →L[ℝ] ℝ) (a : Form (E := V) 1) :
    ‖wedgeOne l a‖ ≤ 2*‖l‖*‖a‖ := by
  apply ContinuousAlternatingMap.opNorm_le_bound _ (by positivity)
  intro m
  have he : ![m 0,m 1] = m := by ext i; fin_cases i <;> rfl
  rw [← he,wedgeOne_apply_two,Real.norm_eq_abs,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ ≤ |l (m 0)*a ![m 1]|+|l (m 1)*a ![m 0]| := by simpa only [Real.norm_eq_abs] using norm_sub_le (l (m 0)*a ![m 1]) (l (m 1)*a ![m 0])
    _ = |l (m 0)| *|a ![m 1]|+|l (m 1)| *|a ![m 0]| := by rw [abs_mul,abs_mul]
    _ ≤ (‖l‖*‖m 0‖)*(‖a‖*‖m 1‖)+(‖l‖*‖m 1‖)*(‖a‖*‖m 0‖) := by
      apply add_le_add <;> apply mul_le_mul
      · exact l.le_opNorm _
      · exact one_eval_norm _ _
      · positivity
      · positivity
      · exact l.le_opNorm _
      · exact one_eval_norm _ _
      · positivity
      · positivity
    _ = _ := by ring

end TamingCompatibility.ExteriorForms

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactPairingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupContinuousLinearMapRealIdFormSpaceOfNatNat
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealContinuousLinearMapIdFormSpaceOfNatNat
omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.concentrationCompact_domain {p : X} (D : ParametrixData J α ht p) :
    D.concentrationCompact ⊆ D.chart.domain := by
  rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
  · exact (D.physicalCompact_domain hxy).1
  · exact (D.physicalCompact_domain hxy).2

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.concentrationPairing_bound {p : X} (D : ParametrixData J α ht p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ D.concentrationCompact,
      ‖MetricForms.pairingCLM (coordinateMetric J α ht p y) 2‖ ≤ C := by
  have hc := MetricForms.pairingCLM_two_smooth (coordinateMetric J α ht p)
    (by simp [Space]) D.chart.frame D.chart.frame_smooth D.chart.frame_gram
  obtain ⟨C,hC⟩ := D.concentrationCompact_compact.exists_bound_of_continuousOn
    (f := fun y => MetricForms.pairingCLM (coordinateMetric J α ht p y) 2)
    (hc.continuousOn.mono D.concentrationCompact_domain)
  exact ⟨max C 0,le_max_right _ _,fun y hy => (hC y hy).trans (le_max_left _ _)⟩

include hE in
omit [T2Space X] [CompactSpace X] in
lemma normalizedFrameEncode_chart_bound (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : TwoForm X) (y : Space), y ∈ (E p).concentrationCompact →
      ‖normalizedFrameEncode A J α ht E ((extChartAt Model p.val).symm y)
        (a ((extChartAt Model p.val).symm y))‖ ≤
          C*‖ManifoldForms.pullback a (extChartAt Model p.val).symm y‖ := by
  obtain ⟨C,hC,hbound⟩ := (E p).concentrationPairing_bound
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,fun a y hy => ?_⟩
  have he := normalizedFrameEncode_inner A J α ht E hE a a ((extChartAt Model p.val).symm y)
  rw [real_inner_self_eq_norm_sq] at he
  have hp := GeometricAdjoint.pairing_two_chart J α ht p.val a a ((E p).concentrationCompact_target hy)
  rw [← hp] at he
  let v := ManifoldForms.pullback a (extChartAt Model p.val).symm y
  have hb : MetricForms.pairing (coordinateMetric J α ht p.val y) v v ≤ C*‖v‖^2 := by
    calc
      _ ≤ ‖MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2 v v‖ := le_abs_self _
      _ ≤ ‖MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2 v‖*‖v‖ :=
        (MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2 v).le_opNorm v
      _ ≤ (‖MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2‖*‖v‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right ((MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2).le_opNorm v) (norm_nonneg _)
      _ ≤ (C*‖v‖)*‖v‖ := by gcongr; exact hbound y hy
      _ = _ := by ring
  have hroot := Real.sq_sqrt hC
  have hp' : 0 ≤ Real.sqrt C*‖v‖ := by positivity
  have he' : (Real.sqrt C*‖v‖)^2 = C*‖v‖^2 := by rw [mul_pow,hroot]
  change _ ≤ Real.sqrt C*‖v‖
  nlinarith [he,hb,norm_nonneg (normalizedFrameEncode A J α ht E ((extChartAt Model p.val).symm y) (a ((extChartAt Model p.val).symm y)))]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration ContinuousAlternatingMap
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma concentrationPatch_differential_chart
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    ManifoldForms.pullback (scalarDifferential (concentrationPatch A J α hs ht E μ p r))
      (extChartAt Model p.val).symm z =
      ofSubsingletonLIE (0 : Fin 1)
        (localConcentration A J α hs ht E μ p r z • fderiv ℝ (coordinatePartition A p) z+
          coordinatePartition A p z • fderiv ℝ (localConcentration A J α hs ht E μ p r) z) := by
  rw [pullback_scalarDifferential
    ((concentrationPatch_smooth A J α hs ht E μ p hr).mdifferentiable (by simp) _)
    (((contMDiffOn_extChartAt_symm (n := ∞) p.val) z hz).contMDiffAt
      ((isOpen_extChartAt_target p.val).mem_nhds hz) |>.mdifferentiableAt (by simp))]
  unfold concentrationPatch
  rw [scalarChartLift_fderiv p.val _ hz]
  congr 1
  simpa only [Pi.mul_apply,add_comm] using fderiv_fun_mul ((coordinatePartition_smooth_compact A p).1.differentiable (by simp) z)
    ((localConcentration_smooth A J α hs ht E μ p hr).differentiable (by simp) z)

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_differential_zero_off
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (p : A.centers) (r : ℝ)
    {x : X} (hx : x ∉ tsupport (A.partition p)) :
    scalarDifferential (concentrationPatch A J α hs ht E μ p r) x = 0 := by
  have he : concentrationPatch A J α hs ht E μ p r =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hopen : IsOpen ((tsupport (A.partition p))ᶜ) := (isClosed_tsupport _).isOpen_compl
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [concentrationPatch_apply, image_eq_zero_of_notMem_tsupport (f := (A.partition p : X → ℝ)) hy,zero_mul]
  unfold scalarDifferential
  rw [he.mfderiv_eq,mfderiv_const]
  change (ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)) (0 : Space →L[ℝ] ℝ) = 0
  exact _root_.map_zero _

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_wedge_zero_off
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (p : A.centers) (r : ℝ)
    (θ : Form X 1) {x : X} (hx : x ∉ tsupport (A.partition p)) :
    ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ x = 0 := by
  unfold ManifoldForms.wedgeOne
  rw [concentrationPatch_differential_zero_off A J α hs ht E μ p r hx]
  change ExteriorForms.wedgeOne ((ofSubsingletonLIE (0 : Fin 1)).symm (0 : ExteriorForms.Form (E := Space) 1)) _ = _
  rw [_root_.map_zero]
  exact (ExteriorForms.wedgeOneRight (E := Space) (θ x)).map_zero

lemma concentrationPatch_wedge_chart
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) (θ : Form X 1)
    {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    ManifoldForms.pullback
      (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ)
      (extChartAt Model p.val).symm z =
      ExteriorForms.wedgeOne
        (localConcentration A J α hs ht E μ p r z • fderiv ℝ (coordinatePartition A p) z+
          coordinatePartition A p z • fderiv ℝ (localConcentration A J α hs ht E μ p r) z)
        (ManifoldForms.pullback θ (extChartAt Model p.val).symm z) := by
  rw [ManifoldForms.pullback_wedgeOne]
  dsimp only
  rw [concentrationPatch_differential_chart A J α hs ht E μ p hr hz]
  congr 1

omit [T2Space X] [CompactSpace X] in
lemma concentration_theta_bound (p : A.centers) (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ (E p).concentrationCompact,
      ‖ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (E p).concentrationCompact_compact.exists_bound_of_continuousOn
    ((smooth_chart θ.val θ.property p.val).continuousOn.mono (E p).concentrationCompact_target)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (hC z hz).trans (le_max_left _ _)⟩

omit [T2Space X] in
lemma concentration_partition_derivative_bound (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ (E p).concentrationCompact,
      ‖fderiv ℝ (coordinatePartition A p) z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (E p).concentrationCompact_compact.exists_bound_of_continuousOn
    (((coordinatePartition_smooth_compact A p).1.continuous_fderiv (by simp)).continuousOn)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (hC z hz).trans (le_max_left _ _)⟩
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration ContinuousAlternatingMap
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma concentrationPatch_coefficient_bound (p : A.centers) (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
      [IsFiniteMeasure μ], ∀ r : ℝ, ∀ _hr : 0 < r,
      ∀ x : X, x ∈ tsupport (A.partition p) →
      ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val x)‖ ≤
      C*(localConcentration A J α hs ht E μ p r (extChartAt Model p.val x)+
        A.partition p x*‖fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x)‖) := by
  obtain ⟨B,hB,hθ⟩ := concentration_theta_bound A J α ht E p θ
  obtain ⟨D,hD,hd⟩ := concentration_partition_derivative_bound A J α ht E p
  obtain ⟨M,hM,hcoef⟩ := normalizedFrameEncode_chart_bound A J α ht E hE p
  refine ⟨M*2*B*(D+1),by positivity,fun μ _ r hr x hx => ?_⟩
  have hz := (E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)
  have htgt := (E p).concentrationCompact_target hz
  let z := extChartAt Model p.val x
  let f := localConcentration A J α hs ht E μ p r
  have hf : 0 ≤ f z := localConcentration_nonneg A J α hs ht E μ p r z
  have hχ := A.partition.nonneg p x
  have hnorm : ‖f z • fderiv ℝ (coordinatePartition A p) z+A.partition p x • fderiv ℝ f z‖ ≤
      f z*D+A.partition p x*‖fderiv ℝ f z‖ := by
    calc
      _ ≤ ‖f z • fderiv ℝ (coordinatePartition A p) z‖+‖A.partition p x • fderiv ℝ f z‖ := norm_add_le _ _
      _ = f z*‖fderiv ℝ (coordinatePartition A p) z‖+A.partition p x*‖fderiv ℝ f z‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hf,abs_of_nonneg hχ]
      _ ≤ _ := by gcongr; exact hd z hz
  have hh := hcoef (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val) z hz
  rw [(extChartAt Model p.val).left_inv (A.subordinate p hx)] at hh
  rw [concentrationPatch_wedge_chart A J α hs ht E μ p hr θ.val htgt,
    coordinatePartition_apply A p (A.subordinate p hx)] at hh
  have hw := ExteriorForms.scalar_wedge_norm
    (f z • fderiv ℝ (coordinatePartition A p) z+A.partition p x • fderiv ℝ f z)
    (ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z)
  have hb := hh.trans (mul_le_mul_of_nonneg_left
    (hw.trans (mul_le_mul (mul_le_mul_of_nonneg_left hnorm (by norm_num)) (hθ z hz) (norm_nonneg _) (by positivity))) hM)
  have hb' : 0 ≤ M*2*B := by positivity
  have he : f z*D+A.partition p x*‖fderiv ℝ f z‖ ≤
      (D+1)*(f z+A.partition p x*‖fderiv ℝ f z‖) := by nlinarith [mul_nonneg hχ (norm_nonneg (fderiv ℝ f z))]
  calc
    _ ≤ M*(2*(f z*D+A.partition p x*‖fderiv ℝ f z‖)*B) := hb
    _ = (M*2*B)*(f z*D+A.partition p x*‖fderiv ℝ f z‖) := by ring
    _ ≤ (M*2*B)*((D+1)*(f z+A.partition p x*‖fderiv ℝ f z‖)) := mul_le_mul_of_nonneg_left he hb'
    _ = _ := by dsimp only [f,z] <;> ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfile_le_one {r : ℝ} (hr : 0 < r) (x y : X) : physicalProfile J α hs ht r x y ≤ 1 := by
  apply pow_le_one₀ (by positivity)
  apply inv_le_one_of_one_le₀
  have : 0 ≤ (hermitianEDist J α hs ht x y).toReal/r := by positivity
  linarith

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_symm (r : ℝ) (x y : X) : physicalProfile J α hs ht r x y = physicalProfile J α hs ht r y x := by
  let := geometricMetricSpace J α hs ht
  change ((1+dist x y/r)⁻¹)^6 = ((1+dist y x/r)⁻¹)^6
  rw [dist_comm]

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfileMass_nonneg
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) (x : X) :
    0 ≤ physicalProfileMass J α hs ht μ r x :=
  integral_nonneg (fun u => physicalProfile_nonneg J α hs ht r x u.val.proj)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
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

lemma radialCoefficient_linear_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t*t ≤ (8/r^3)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by
    field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^3)*(r^6/(r+t)^6) = 8*r^3/(r+t)^6 := by field_simp
  rw [he',div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : r*t ≤ r^2+t^2 := by nlinarith [sq_nonneg (r-t)]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ r*t)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^3)
  nlinarith
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CutGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma cutKernel_gradient_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ z : V,
      ‖fderiv ℝ (cutKernel η r) z‖ ≤ (48/r^3)*((1+‖z‖/r)⁻¹)^6+C*r^4 := by
  obtain ⟨C,hC,hbound⟩ := cutKernel_deriv_bound η hη hηc hη0 hη1 ha hηone
  refine ⟨C,hC,fun r hr z => ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_⟩
  intro w
  rw [Real.norm_eq_abs]
  have hinner := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z w)
    (show 0 ≤ (6:ℝ)*radialCoefficient r ‖z‖ from mul_nonneg (by norm_num) (radialCoefficient_nonneg _ _))
  have hprofile := mul_le_mul_of_nonneg_right
    (radialCoefficient_linear_profile hr (norm_nonneg z)) (by positivity : 0 ≤ 6*‖w‖)
  have hder := hbound r hr z w
  have he : (8/r^3)*((1+‖z‖/r)⁻¹)^6*(6*‖w‖) = (48/r^3)*((1+‖z‖/r)⁻¹)^6*‖w‖ := by ring
  rw [he] at hprofile
  nlinarith
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PhysicalSchur
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
variable {V : Type*} [NormedAddCommGroup V]

lemma physicalQError_product_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (q : X → V) (hq : Integrable q (geometricVolume A J α)) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    Integrable (fun uy : MetricUnit (hermitianMetric J α hs ht) × X =>
      ‖q uy.2‖*physicalProfile J α hs ht (L*r) uy.1.val.proj uy.2/r^3)
        (μ.prod (geometricVolume A J α)) := by
  let := geometricVolume_finite A J α hs ht
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hm : AEStronglyMeasurable (fun uy : MetricUnit (hermitianMetric J α hs ht) × X =>
      physicalProfile J α hs ht (L*r) uy.1.val.proj uy.2) (μ.prod (geometricVolume A J α)) :=
    ((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      ((hp.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
  apply ((hq.norm.comp_snd μ).mul_bdd hm (c := 1) ?_).div_const
  exact Eventually.of_forall fun uy => by
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalProfile_nonneg J α hs ht _ _ _)]
    exact physicalProfile_le_one J α hs ht (mul_pos hL hr) _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationPhysicalBound
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma compact_chart_profile_bound (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : X, x ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      u ∈ unitChartDomain J α hs ht p K → ∀ r : ℝ, 0 < r →
      ((1+‖extChartAt Model p x-unitChartBase J α hs ht p u‖/r)⁻¹)^6 ≤
        physicalProfile J α hs ht (L*r) x u.val.proj := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨L₀,hL₀⟩ := chartInverse_compact_lipschitz J α hs ht p K hK hKT
  let L : ℝ := (L₀:ℝ)+1
  have hL : 0 < L := by dsimp [L] <;> positivity
  refine ⟨L,hL,fun x hx hxK u hu r hr => ?_⟩
  have humem := unitChart_mem J α hs ht p hKT hu
  have hphys := hL₀.dist_le_mul _ hxK _ humem.2
  change dist ((extChartAt Model p).symm (extChartAt Model p x))
    ((extChartAt Model p).symm (unitChartBase J α hs ht p u)) ≤ _ at hphys
  simp only [unitChartBase] at hphys
  rw [(extChartAt Model p).left_inv hx,(extChartAt Model p).left_inv humem.1,dist_eq_norm] at hphys
  have htransport : dist x u.val.proj ≤ L*‖extChartAt Model p x-unitChartBase J α hs ht p u‖ :=
    hphys.trans (mul_le_mul_of_nonneg_right (by dsimp [L] <;> linarith) (norm_nonneg _))
  have hdiv : dist x u.val.proj/(L*r) ≤ ‖extChartAt Model p x-unitChartBase J α hs ht p u‖/r := by
    apply (div_le_iff₀ (mul_pos hL hr)).mpr
    calc
      _ ≤ L*‖extChartAt Model p x-unitChartBase J α hs ht p u‖ := htransport
      _ = _ := by field_simp
  change _ ≤ ((1+dist x u.val.proj/(L*r))⁻¹)^6
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 6

include hE in
omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma concentrationDensity_physical_bound (p : A.centers) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u ≤
        (C/r^2)*physicalProfile J α hs ht (L*r) x u.val.proj := by
  obtain ⟨L,hL,hprofile⟩ := compact_chart_profile_bound J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨_,P,_,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  refine ⟨8*P,L,by positivity,hL,fun x hx r hr u => ?_⟩
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · have hxK := (E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)
    have hp := hprofile x (A.subordinate p hx) hxK u hu r hr
    rw [concentrationDensity,indicator_of_mem hu]
    calc
      _ ≤ P*rationalKernel r (extChartAt Model p.val x-unitChartBase J α hs ht p.val u) :=
        mul_le_mul (harea u hu).2
          (cutKernel_le _ (fun z => (E p).concentrationCutoff.bump.le_one (x := z)) _ _)
          (cutKernel_nonneg _ (fun z => (E p).concentrationCutoff.bump.nonneg (x := z)) _ _) hP.le
      _ ≤ P*((8/r^2)*((1+‖extChartAt Model p.val x-unitChartBase J α hs ht p.val u‖/r)⁻¹)^6) :=
        mul_le_mul_of_nonneg_left (rationalKernel_profile hr _) hP.le
      _ ≤ P*((8/r^2)*physicalProfile J α hs ht (L*r) x u.val.proj) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) hP.le
      _ = _ := by ring
  · rw [concentrationDensity,indicator_of_notMem hu]
    exact mul_nonneg (by positivity) (physicalProfile_nonneg J α hs ht _ _ _)

include hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma localConcentration_physical_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] (p : A.centers) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r → localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        (C/r^2)*physicalProfileMass J α hs ht μ (L*r) x := by
  obtain ⟨C,L,hC,hL,hbound⟩ := concentrationDensity_physical_bound A J α hs ht E hE p
  refine ⟨C,L,hC,hL,fun x hx r hr => ?_⟩
  rw [localConcentration_integral A J α hs ht E μ p hr,physicalProfileMass,←integral_const_mul]
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hmap : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => (x,u.val.proj)) := continuous_const.prodMk hp
  have hh := (physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp hmap
  exact integral_mono (concentrationDensity_integrable A J α hs ht E μ p hr _)
    ((hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _)
    (hbound x hx r hr)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationPatchError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma localConcentration_gradient_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r →
      ‖fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x)‖ ≤
        B*physicalGradientMass J α hs ht μ L r x+C*r^4 := by
  obtain ⟨L,hL,hprofile⟩ := compact_chart_profile_bound J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨_,P,_,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hone : ∀ z : Space, ‖z‖ < (E p).concentrationCutoff.radius/2 → (E p).concentrationCutoff.bump z = 1 := by
    intro z hz
    apply ContDiffBump.one_of_mem_closedBall
    change dist z 0 ≤ (E p).concentrationCutoff.radius/2
    simpa only [dist_zero_right] using hz.le
  obtain ⟨C,hC,hder⟩ := cutKernel_gradient_bound
    (E p).concentrationCutoff.bump (E p).concentrationCutoff.bump.contDiff
    (E p).concentrationCutoff.bump.hasCompactSupport
    (fun z => (E p).concentrationCutoff.bump.nonneg (x := z))
    (fun z => (E p).concentrationCutoff.bump.le_one (x := z))
    (by linarith [(E p).concentrationCutoff.positive] : 0 < (E p).concentrationCutoff.radius/2) hone
  refine ⟨48*P,P*C,L,by positivity,by positivity,hL,fun x hx r hr => ?_⟩
  let f := fun u : MetricUnit (hermitianMetric J α hs ht) =>
    (48*P/r^3)*physicalProfile J α hs ht (L*r) x u.val.proj+P*C*r^4
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hf : Integrable f μ := by
    exact (((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      (continuous_const.prodMk hp)).const_mul _ |>.add continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn (u) : 0 ≤ f u := add_nonneg
    (mul_nonneg (by positivity) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)
  have he : ∫ u, f u ∂μ = 48*P*physicalGradientMass J α hs ht μ L r x+P*C*r^4 := by
    have hi : Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) => (48*P/r^3)*physicalProfile J α hs ht (L*r) x u.val.proj) μ := (((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      (continuous_const.prodMk hp)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul (48*P/r^3)
    rw [show f = (fun u => (48*P/r^3)*physicalProfile J α hs ht (L*r) x u.val.proj+P*C*r^4) from rfl,
      integral_add hi (integrable_const _),integral_const_mul,integral_const,probReal_univ,one_smul]
    dsimp only [physicalGradientMass,physicalProfileMass]
    ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by rw [←he]; exact integral_nonneg hn)
  intro w
  change ‖fderiv ℝ (planeConvolution J α hs ht p.val (E p).concentrationCompact μ
    (cutKernel (E p).concentrationCutoff.bump r)) (extChartAt Model p.val x) w‖ ≤ _
  rw [planeConvolution_deriv J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff)
    (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r),←he,←integral_mul_const]
  apply norm_integral_le_of_norm_le (hf.mul_const ‖w‖)
  apply ae_of_all
  intro u
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · rw [indicator_of_mem hu,norm_mul,Real.norm_eq_abs,abs_of_nonneg
      (show 0 ≤ unitChartArea J α hs ht p.val u from mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hprof := hprofile x (A.subordinate p hx)
      ((E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)) u hu r hr
    have hd := (hder r hr (extChartAt Model p.val x-unitChartBase J α hs ht p.val u)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hprof (by positivity : 0 ≤ 48/r^3)) le_rfl)
    have hw := (fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
      (extChartAt Model p.val x-unitChartBase J α hs ht p.val u)).le_opNorm w
    have hww := hw.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
    exact (mul_le_mul (harea u hu).2 hww (norm_nonneg _) hP.le).trans_eq (by dsimp only [f] <;> ring)
  · rw [indicator_of_notMem hu,norm_zero]
    exact mul_nonneg (hn u) (norm_nonneg _)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationPatchQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma physicalGradientMass_mul_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] (q : X → V)
    (hq : Integrable q (geometricVolume A J α)) {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    Integrable (fun x => ‖q x‖*physicalGradientMass J α hs ht μ L r x) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  apply (physicalQError_product_integrable A J α hs ht μ q hq hL hr).integral_prod_right.congr
  apply Eventually.of_forall
  intro x
  simp_rw [physicalProfile_symm J α hs ht (L*r) _ x]
  rw [integral_div,integral_const_mul]
  simp only [physicalGradientMass,physicalProfileMass,mul_div_assoc]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalGradientMass_nonneg
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (L : ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ physicalGradientMass J α hs ht μ L r x :=
  div_nonneg (physicalProfileMass_nonneg J α hs ht μ _ _) (by positivity)

include hE in
lemma concentrationPatch_Q_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) (p : A.centers) :
    ∃ e : ℝ → X → ℝ,
      (∀ r, 0 < r → ∀ x, 0 ≤ e r x) ∧
      (∀ r, 0 < r → Integrable (e r) (geometricVolume A J α)) ∧
      Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x,
        ‖l2Coefficients A J α hs ht E hE Q x‖ *
          ‖normalizedFrameEncode A J α ht E x
            (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val x)‖ ≤ C*e r x := by
  let := geometricVolume_finite A J α hs ht
  let q := l2Coefficients A J α hs ht E hE Q
  have hq : Integrable q (geometricVolume A J α) := (Lp.memLp q).integrable (by norm_num)
  obtain ⟨B,C,L,hB,hC,hL,hgrad⟩ := localConcentration_gradient_bound A J α hs ht E hE μ p
  obtain ⟨D,L',hD,hL',hlocal⟩ := localConcentration_physical_bound A J α hs ht E hE μ p
  let e := fun r x => D*(‖q x‖*physicalGradientMass J α hs ht μ L' r x)+
    B*(‖q x‖*physicalGradientMass J α hs ht μ L r x)+C*r^4*‖q x‖
  have he (r) (hr : 0 < r) (x) : 0 ≤ e r x := by
    exact add_nonneg (add_nonneg
      (mul_nonneg hD (mul_nonneg (norm_nonneg _) (physicalGradientMass_nonneg J α hs ht μ L' hr x)))
      (mul_nonneg hB (mul_nonneg (norm_nonneg _) (physicalGradientMass_nonneg J α hs ht μ L hr x))))
      (mul_nonneg (by positivity) (norm_nonneg _))
  have hi (r) (hr : 0 < r) : Integrable (e r) (geometricVolume A J α) :=
    (((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL' hr).const_mul D).add
      ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL hr).const_mul B)).add
      (hq.norm.const_mul (C*r^4))
  have heq (r) (hr : 0 < r) : (∫ x, e r x ∂geometricVolume A J α) =
      D*(∫ x, ‖q x‖*physicalGradientMass J α hs ht μ L' r x ∂geometricVolume A J α)+
      B*(∫ x, ‖q x‖*physicalGradientMass J α hs ht μ L r x ∂geometricVolume A J α)+
      (C*r^4)*(∫ x, ‖q x‖ ∂geometricVolume A J α) := by
    dsimp only [e]
    erw [integral_add (((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL' hr).const_mul D).add
      ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL hr).const_mul B)) (hq.norm.const_mul (C*r^4)),
      integral_add ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL' hr).const_mul D)
        ((physicalGradientMass_mul_integrable A J α hs ht μ q hq hL hr).const_mul B),
      integral_const_mul,integral_const_mul,integral_const_mul]
  have he0 : Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := physicalGradientMass_L2_limit A J α hs ht μ hann q (Lp.memLp q) hL'
    have h2 := physicalGradientMass_L2_limit A J α hs ht μ hann q (Lp.memLp q) hL
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have hh := ((h1.const_mul D).add (h2.const_mul B)).add (((hr.pow 4).const_mul C).mul_const (∫ x, ‖q x‖ ∂geometricVolume A J α))
    simp only [zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul,add_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (heq r hr).symm
  refine ⟨e,he,hi,he0,fun θ => ?_⟩
  obtain ⟨K,hK,hcoef⟩ := concentrationPatch_coefficient_bound A J α hs ht E hE p θ
  refine ⟨K,hK,fun r hr hr1 x => ?_⟩
  by_cases hx : x ∈ tsupport (A.partition p)
  · have hg := hgrad x hx r hr
    have hl := hlocal x hx r hr
    have hχ := A.partition.nonneg p x
    have hχ1 := A.partition.le_one p x
    have hp : (D/r^2)*physicalProfileMass J α hs ht μ (L'*r) x ≤
        D*physicalGradientMass J α hs ht μ L' r x := by
      calc
        _ = D*r*physicalGradientMass J α hs ht μ L' r x := by dsimp only [physicalGradientMass]; field_simp
        _ = (D*physicalGradientMass J α hs ht μ L' r x)*r := by ring
        _ ≤ (D*physicalGradientMass J α hs ht μ L' r x)*1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hD (physicalGradientMass_nonneg J α hs ht μ L' hr x))
        _ = _ := mul_one _
    have hb : localConcentration A J α hs ht E μ p r (extChartAt Model p.val x)+
        A.partition p x*‖fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x)‖ ≤
      D*physicalGradientMass J α hs ht μ L' r x+B*physicalGradientMass J α hs ht μ L r x+C*r^4 := by
      have hmul := mul_le_of_le_one_left (norm_nonneg (fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x))) hχ1
      linarith
    have hh := mul_le_mul_of_nonneg_left ((hcoef μ r hr x hx).trans (mul_le_mul_of_nonneg_left hb hK)) (norm_nonneg (q x))
    exact hh.trans_eq (by dsimp only [e,q] <;> ring)
  · rw [concentrationPatch_wedge_zero_off A J α hs ht E μ p r θ.val hx]
    erw [map_zero,norm_zero,mul_zero]
    exact mul_nonneg hK (he r hr x)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationGlobalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma globalConcentration_wedge
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (θ : Form X 1) :
    ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ =
      ∑ p : A.centers, ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ := by
  classical
  rw [globalConcentration,scalarDifferential_sum _ _
    (fun p _ => (concentrationPatch_smooth A J α hs ht E μ p hr).mdifferentiable (by simp)),wedgeOne_sum_left]

include hE in
lemma globalConcentration_Q_control_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) :
    ∃ e : ℝ → X → ℝ,
      (∀ r, 0 < r → ∀ x, 0 ≤ e r x) ∧
      (∀ r, 0 < r → Integrable (e r) (geometricVolume A J α)) ∧
      Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x,
        ‖l2Coefficients A J α hs ht E hE Q x‖ *
          ‖normalizedFrameEncode A J α ht E x
            (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val x)‖ ≤ C*e r x := by
  classical
  choose e he hi h0 hb using fun p => concentrationPatch_Q_control A J α hs ht E hE μ hann Q p
  let err := fun r x => ∑ p : A.centers, e p r x
  have hn (r) (hr : 0 < r) (x) : 0 ≤ err r x := Finset.sum_nonneg (fun p _ => he p r hr x)
  have hin (r) (hr : 0 < r) : Integrable (err r) (geometricVolume A J α) := integrable_finsetSum _ (fun p _ => hi p r hr)
  have hlim : Tendsto (fun r => ∫ x, err r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun p _ => h0 p)
    simp only [Finset.sum_const_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (integral_finsetSum _ (fun p _ => hi p r hr)).symm
  refine ⟨err,hn,hin,hlim,fun θ => ?_⟩
  choose C hC hbound using fun p => hb p θ
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr hr1 x => ?_⟩
  rw [globalConcentration_wedge A J α hs ht E μ hr θ.val]
  simp only [Finset.sum_apply]
  erw [_root_.map_sum]
  have hh := mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ
    (fun p : A.centers => normalizedFrameEncode A J α ht E x
      (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val x)))
    (norm_nonneg (l2Coefficients A J α hs ht E hE Q x))
  rw [Finset.mul_sum] at hh
  apply hh.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  have hep : e p r x ≤ err r x := Finset.single_le_sum (fun i _ => he i r hr x) (Finset.mem_univ p)
  exact (hbound p r hr hr1 x).trans (mul_le_mul_of_nonneg_left hep (hC p))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control_oai.{u_1}
