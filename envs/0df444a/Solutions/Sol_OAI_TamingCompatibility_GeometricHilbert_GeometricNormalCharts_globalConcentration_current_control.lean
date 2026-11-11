-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:27:08.820402+00:00
-- url     : https://prove2.me/submissions/51d99c0b-69e4-4010-b4b0-8e2919d61cd3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc020
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_concentration_plane_estimate
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_physicalGradientMass_L2_limit
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_separating_current_second_variation_limit
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_separating_current_variation_limit

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartOverlapControl
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Set Filter GeometricHilbert
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma compact_chart_overlap_control (p q : X) {K : Set X} (hK : IsCompact K)
    (hp : K ⊆ (extChartAt Model p).source) (hq : K ⊆ (extChartAt Model q).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ y : X,
      y ∈ (extChartAt Model p).source →
      ‖extChartAt Model p y-extChartAt Model p x‖ ≤ ε →
      y ∈ (extChartAt Model q).source ∧
      ‖extChartAt Model q y-extChartAt Model q x‖ ≤ C*‖extChartAt Model p y-extChartAt Model p x‖ := by
  let U : Set Space := (extChartAt Model p).target ∩
    (extChartAt Model p).symm ⁻¹' (extChartAt Model q).source
  have hU : IsOpen U := (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) (isOpen_extChartAt_source q)
  let f : Space → Space := extChartAt Model q ∘ (extChartAt Model p).symm
  have hf : ∀ z ∈ U, ContDiffAt ℝ ∞ f z := by
    intro z hz
    exact ((contDiffOn_ext_coord_change (I := Model) (n := ∞) q p) z hz).contDiffAt (hU.mem_nhds hz)
  let L : Set Space := extChartAt Model p '' K
  have hL : IsCompact L := hK.image_of_continuousOn ((continuousOn_extChartAt p).mono hp)
  have hLU : L ⊆ U := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨(extChartAt Model p).map_source (hp hx),by simpa only [mem_preimage,(extChartAt Model p).left_inv (hp hx)] using hq hx⟩
  let O : Set (Space × Space) := (fun z => z.1+z.2) ⁻¹' U
  have hO : IsOpen O := hU.preimage (continuous_fst.add continuous_snd)
  have hLO : L ×ˢ {(0 : Space)} ⊆ O := by
    rintro ⟨z,w⟩ ⟨hz,rfl⟩
    simpa only [O,mem_preimage,add_zero] using hLU hz
  obtain ⟨C,hC,ε,hε,hsub,hbound⟩ := UniformJets.local_linear_bound
    (fun z : Space × Space => f (z.1+z.2)) L hL O hO hLO
    (fun z hz => ContDiffAt.comp (g := f) (f := fun a : Space × Space => a.1+a.2) z
      (hf _ hz) (contDiffAt_fst.add contDiffAt_snd))
  refine ⟨C,hC,ε,hε,fun x hx y hy hxy => ?_⟩
  have hxL : extChartAt Model p x ∈ L := ⟨x,hx,rfl⟩
  have hz : extChartAt Model p x + (extChartAt Model p y-extChartAt Model p x) = extChartAt Model p y := by abel
  have hyU : extChartAt Model p y ∈ U := by
    simpa only [O,mem_preimage,hz] using hsub
      (show (extChartAt Model p x,extChartAt Model p y-extChartAt Model p x) ∈ L ×ˢ Metric.closedBall 0 ε from
        ⟨hxL,by simpa only [Metric.mem_closedBall,dist_zero_right] using hxy⟩)
  refine ⟨by simpa only [U,mem_inter_iff,mem_preimage,(extChartAt Model p).left_inv hy] using hyU.2,?_⟩
  have hb := hbound _ hxL (extChartAt Model p y-extChartAt Model p x) hxy
  simpa only [hz,add_zero,f,Function.comp_apply,(extChartAt Model p).left_inv hy,
    (extChartAt Model p).left_inv (hp hx)] using hb
end TamingCompatibility

end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialUnitCoordinates
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
lemma unitChart_eval (p : X) (β : TwoForm X) (hβ : IsSmooth β)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    ManifoldForms.pullback β (extChartAt Model p).symm (unitChartBase J α hs ht p u)
      ![unitChartVector J α hs ht p u,
        coordinateJ J p (unitChartBase J α hs ht p u) (unitChartVector J α hs ht p u)] =
      unitEvaluation J (hermitianMetric J α hs ht) β hβ u := by
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : u.val.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hu
  have hv : t.symmL ℝ u.val.proj (unitChartVector J α hs ht p u) = u.val.2 := by
    change t.symmL ℝ u.val.proj ((t u.val).2) = _
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb]
    exact t.symmL_continuousLinearMapAt hb _
  dsimp only [unitChartBase]
  rw [pullback_complexLine J β p ((extChartAt Model p).map_source hu),
    inverseChart_derivative p ((extChartAt Model p).map_source hu)]
  change eval β ((extChartAt Model p).symm (extChartAt Model p u.val.proj))
    (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)
    (J.endomorphism _ (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)) = _
  rw [(extChartAt Model p).left_inv hu,hv]
  rfl

end TamingCompatibility.GeometricHilbert.Hermitian

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

end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDirectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma alternating_swap (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) :
    a ![v,u] = -a ![u,v] := by
  have hv : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.map_swap ![u,v] (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_smul_left (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![c • u,v] = c * a ![u,v] := by
  simpa only [smul_eq_mul] using a.vecCons_smul ![v] c u

lemma alternating_smul_right (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![u,c • v] = c * a ![u,v] := by
  rw [alternating_swap,alternating_smul_left,alternating_swap]
  ring

lemma alternating_self (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) : a ![u,u] = 0 :=
  a.map_eq_zero_of_eq ![u,u] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2) ≠ 1)

end TamingCompatibility.UnitaryFrame

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

lemma alternating_area (β : V [⋀^Fin 2]→L[ℝ] ℝ) (a b : V) :
    β ![a,b] = area a b * β ![first a,second a b] := by
  have hsum (u v w : V) : β ![u,v+w] = β ![u,v]+β ![u,w] := by
    rw [UnitaryFrame.alternating_swap]
    have hh := β.vecCons_add ![u] v w
    rw [hh,UnitaryFrame.alternating_swap β v u,UnitaryFrame.alternating_swap β w u]
    ring
  conv_lhs => rw [← first_reconstruct a,reconstruct_second a b]
  rw [hsum,UnitaryFrame.alternating_smul_left,UnitaryFrame.alternating_smul_left,
    UnitaryFrame.alternating_smul_right,UnitaryFrame.alternating_smul_right,
    UnitaryFrame.alternating_self]
  dsimp [area]
  ring

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanUnitPlanes
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

omit [CompactSpace X] [T2Space X] in
lemma unitChartArea_eval (p : X) (β : TwoForm X) (hβ : IsSmooth β)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    unitEvaluation J (hermitianMetric J α hs ht) β hβ u =
      unitChartArea J α hs ht p u *
        ManifoldForms.pullback β (extChartAt Model p).symm (unitChartBase J α hs ht p u)
          ![unitChartFirst J α hs ht p u,unitChartSecond J α hs ht p u] := by
  rw [← unitChart_eval J α hs ht p β hβ u hu]
  exact alternating_area _ _ _

end TamingCompatibility.GeometricHilbert.Hermitian

end
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
lemma rationalKernel_compare {r C : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (z w : V)
    (hz : ‖w‖ ≤ C*‖z‖) : rationalKernel r z ≤ C^6*rationalKernel r w := by
  have hCp : 0 ≤ C := le_trans zero_le_one hC
  have hd : r^2+‖w‖^2 ≤ C^2*(r^2+‖z‖^2) := by
    have hs : ‖w‖^2 ≤ (C*‖z‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hc : 1 ≤ C^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
    nlinarith
  have hd3 := pow_le_pow_left₀ (by positivity : 0 ≤ r^2+‖w‖^2) hd 3
  have hh : (r^2+‖w‖^2)^3 ≤ C^6*(r^2+‖z‖^2)^3 := by
    simpa only [mul_pow,←pow_mul] using hd3
  unfold rationalKernel
  rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ r^4*(C^6*(r^2+‖z‖^2)^3) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneTransverseGraph
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

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneConvolution
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma source_subset : D.source ⊆ (extChartAt Model p).source := Set.inter_subset_left

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
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

omit [T2Space X] [CompactSpace X] in
lemma globalConcentration_nonneg (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (r : ℝ) (x : X) : 0 ≤ globalConcentration A J α hs ht E μ r x := by
  classical
  simp only [globalConcentration,Finset.sum_apply]
  apply Finset.sum_nonneg
  intro p _
  rw [concentrationPatch_apply]
  exact mul_nonneg (A.partition.nonneg _ _) (localConcentration_nonneg A J α hs ht E μ p r _)
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

omit [T2Space X] [CompactSpace X] in
lemma concentrationDensity_nonneg (p : A.centers) (r : ℝ) (b : Space)
    (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ concentrationDensity A J α hs ht E p r b u := by
  apply indicator_nonneg _ u
  intro v _
  apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact cutKernel_nonneg _ (fun z => (E p).concentrationCutoff.bump.nonneg (x := z)) _ _

omit [CompactSpace X] in
lemma localConcentration_integral (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) {r : ℝ} (hr : 0 < r) (b : Space) :
    localConcentration A J α hs ht E μ p r b = ∫ u, concentrationDensity A J α hs ht E p r b u ∂μ := by
  exact planeMeasure_integral J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _
    ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous.comp
      (continuous_const.sub continuous_id))

omit [T2Space X] [CompactSpace X] in
lemma concentrationDensity_near (p : A.centers) {x : X}
    (hx : extChartAt Model p.val x ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hne : ‖extChartAt Model p.val u.val.proj-extChartAt Model p.val x‖ ≤
      (E p).concentrationCutoff.radius/2) (r : ℝ) :
    concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u =
      unitChartArea J α hs ht p.val u * rationalKernel r
        (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) := by
  have hnear : (extChartAt Model p.val x,extChartAt Model p.val u.val.proj) ∈ (E p).physicalCompact :=
    (E p).concentrationCutoff.near _ hx _ (hne.trans (by linarith [(E p).concentrationCutoff.positive]))
  have hbase : extChartAt Model p.val u.val.proj ∈ (E p).concentrationCompact :=
    Or.inr ⟨_,hnear,rfl⟩
  have hmem : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
    ⟨extChartAt Model p.val u.val.proj,hbase,(extChartAt Model p.val).left_inv hu⟩
  have hone : (E p).concentrationCutoff.bump (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) 0 ≤ (E p).concentrationCutoff.radius/2
    rwa [dist_zero_right,norm_sub_rev]
  simp only [concentrationDensity,indicator_of_mem hmem,cutKernel,unitChartBase,hone,one_mul]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationCompare
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
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
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma concentrationDensity_compare (p q : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X,
      x ∈ tsupport (A.partition p) → x ∈ tsupport (A.partition q) →
      ∀ r : ℝ, 0 < r → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u ≤
        C*concentrationDensity A J α hs ht E q r (extChartAt Model q.val x) u+B*r^4 := by
  let K := tsupport (A.partition p) ∩ tsupport (A.partition q)
  have hK : IsCompact K := (isClosed_tsupport (A.partition p)).isCompact.inter_right (isClosed_tsupport _)
  obtain ⟨L,hL,δ,hδ,hnear⟩ := compact_chart_overlap_control p.val q.val hK
    (fun _ hx => A.subordinate p hx.1) (fun _ hx => A.subordinate q hx.2)
  obtain ⟨_,P,_,hP,hPbound⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨m,_,hm,_,hmbound⟩ := unitChartArea_bounds J α hs ht q.val
    (E q).concentrationCompact_compact (E q).concentrationCompact_target
  let M := max L 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let ε := min δ ((E q).concentrationCutoff.radius/(2*M))
  have hε : 0 < ε := lt_min hδ (div_pos (E q).concentrationCutoff.positive (by positivity))
  refine ⟨P*M^6/m,P/ε^6,by positivity,by positivity,fun x hxp hxq r hr u => ?_⟩
  have hq0 := concentrationDensity_nonneg A J α hs ht E q r (extChartAt Model q.val x) u
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · have harea : unitChartArea J α hs ht p.val u ≤ P := (hPbound u hu).2
    have hpbound : concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u ≤
        P*rationalKernel r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) := by
      rw [concentrationDensity,indicator_of_mem hu]
      exact mul_le_mul harea (cutKernel_le _ (fun z => (E p).concentrationCutoff.bump.le_one (x := z)) _ _)
        (cutKernel_nonneg _ (fun z => (E p).concentrationCutoff.bump.nonneg (x := z)) _ _) hP.le
    by_cases hz : ‖extChartAt Model p.val u.val.proj-extChartAt Model p.val x‖ ≤ ε
    · have hnv := hnear x ⟨hxp,hxq⟩ u.val.proj
        (unitChart_mem J α hs ht p.val (E p).concentrationCompact_target hu).1
        (hz.trans (min_le_left _ _))
      have hzq : ‖extChartAt Model q.val u.val.proj-extChartAt Model q.val x‖ ≤
          (E q).concentrationCutoff.radius/2 := by
        calc
          _ ≤ M*‖extChartAt Model p.val u.val.proj-extChartAt Model p.val x‖ :=
            hnv.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
          _ ≤ M*((E q).concentrationCutoff.radius/(2*M)) :=
            mul_le_mul_of_nonneg_left (hz.trans (min_le_right _ _)) hMp.le
          _ = _ := by field_simp
      have hcenter := partition_center_ball A J α ht E hE q hxq
      have hphys := (E q).concentrationCutoff.near _ hcenter
        (extChartAt Model q.val u.val.proj) (hzq.trans (by linarith [(E q).concentrationCutoff.positive]))
      have huq : u ∈ unitChartDomain J α hs ht q.val (E q).concentrationCompact :=
        ⟨extChartAt Model q.val u.val.proj,Or.inr ⟨_,hphys,rfl⟩,(extChartAt Model q.val).left_inv hnv.1⟩
      have hqa := (hmbound u huq).1
      have hqeq := concentrationDensity_near A J α hs ht E q hcenter u hnv.1 hzq r
      have hrat : rationalKernel r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) ≤
          M^6*rationalKernel r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj) := by
        apply rationalKernel_compare hr hM
        simpa only [norm_sub_rev] using hnv.2.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      calc
        _ ≤ P*(M^6*rationalKernel r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj)) :=
          hpbound.trans (mul_le_mul_of_nonneg_left hrat hP.le)
        _ ≤ (P*M^6/m)*(unitChartArea J α hs ht q.val u *
            rationalKernel r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj)) := by
          have hpa : P*M^6 ≤ (P*M^6/m)*unitChartArea J α hs ht q.val u := by
            have hh := mul_le_mul_of_nonneg_left hqa (by positivity : 0 ≤ P*M^6/m)
            rwa [div_mul_cancel₀ _ hm.ne'] at hh
          nlinarith [mul_le_mul_of_nonneg_right hpa
            (rationalKernel_nonneg r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj))]
        _ ≤ _ := by rw [←hqeq]; exact le_add_of_nonneg_right (by positivity)
    · have haway : ε ≤ ‖extChartAt Model p.val x-extChartAt Model p.val u.val.proj‖ := by
        simpa only [norm_sub_rev] using le_of_lt (lt_of_not_ge hz)
      have hh := mul_le_mul_of_nonneg_left (rationalKernel_away hε haway (r := r)) hP.le
      have he : P*(r^4/ε^6) = (P/ε^6)*r^4 := by ring
      rw [he] at hh
      exact (hpbound.trans hh).trans (le_add_of_nonneg_left (by positivity))
  · rw [concentrationDensity,indicator_of_notMem hu]
    positivity

include hE in
lemma localConcentration_compare
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (p q : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X,
      x ∈ tsupport (A.partition p) → x ∈ tsupport (A.partition q) →
      ∀ r : ℝ, 0 < r →
      localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        C*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x)+B*r^4 := by
  obtain ⟨C,B,hC,hB,hb⟩ := concentrationDensity_compare A J α hs ht E hE p q
  refine ⟨C,B,hC,hB,fun x hx hy r hr => ?_⟩
  rw [localConcentration_integral A J α hs ht E μ p hr,
    localConcentration_integral A J α hs ht E μ q hr]
  have hp := concentrationDensity_integrable A J α hs ht E μ p hr (extChartAt Model p.val x)
  have hq := concentrationDensity_integrable A J α hs ht E μ q hr (extChartAt Model q.val x)
  have hh := integral_mono hp ((hq.const_mul C).add (integrable_const (B*r^4))) (hb x hx hy r hr)
  simpa only [Pi.add_apply,integral_add (hq.const_mul C) (integrable_const (B*r^4)),integral_const_mul,integral_const,
    probReal_univ,one_smul] using hh
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
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma localConcentration_global_compare
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (p : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r →
      localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        C*globalConcentration A J α hs ht E μ r x+B*r^4 := by
  classical
  choose c b hc hb hh using fun q => localConcentration_compare A J α hs ht E hE μ p q
  let C := ∑ q : A.centers, c q
  let B := ∑ q : A.centers, b q
  have hC : 0 ≤ C := Finset.sum_nonneg (fun q _ => hc q)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun q _ => hb q)
  have hcC (q : A.centers) : c q ≤ C := Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ q)
  have hbB (q : A.centers) : b q ≤ B := Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ q)
  refine ⟨C,B,hC,hB,fun x hx r hr => ?_⟩
  have hq (q : A.centers) :
      A.partition q x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        C*(A.partition q x*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x))+
          A.partition q x*(B*r^4) := by
    by_cases hz : A.partition q x = 0
    · simp only [hz,zero_mul,mul_zero,add_zero,le_refl]
    · have hqx : x ∈ tsupport (A.partition q) := subset_tsupport _ (Function.mem_support.mpr hz)
      have hlocal := hh q x hx hqx r hr
      have hglobal : localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
          C*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x)+B*r^4 :=
        hlocal.trans (add_le_add
          (mul_le_mul_of_nonneg_right (hcC q) (localConcentration_nonneg A J α hs ht E μ q r _))
          (mul_le_mul_of_nonneg_right (hbB q) (by positivity)))
      have hm := mul_le_mul_of_nonneg_left hglobal (A.partition.nonneg q x)
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun q _ => hq q)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,partition_sum,one_mul] at hsum
  have he : globalConcentration A J α hs ht E μ r x =
      ∑ q : A.centers, A.partition q x*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x) := by
    simp only [globalConcentration,Finset.sum_apply,concentrationPatch_apply]
  rwa [←he] at hsum
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

lemma scalar_wedge_unit (l : V →L[ℝ] ℝ) (a : Form (E := V) 1) (u v : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |wedgeOne l a ![u,v]| ≤ ‖a‖*(|l u|+|l v|) := by
  have ha := one_eval_norm a u
  have hb := one_eval_norm a v
  rw [hu,mul_one] at ha
  rw [hv,mul_one] at hb
  rw [wedgeOne_apply_two]
  calc
    _ ≤ |l u*a ![v]|+|l v*a ![u]| := by simpa only [Real.norm_eq_abs] using norm_sub_le (l u*a ![v]) (l v*a ![u])
    _ ≤ |l u| *‖a‖+|l v| *‖a‖ := by rw [abs_mul,abs_mul]; gcongr
    _ = _ := by ring
end TamingCompatibility.ExteriorForms

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
lemma concentrationPatch_tangential_bound (p : A.centers) (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
      [IsFiniteMeasure μ], ∀ r : ℝ, ∀ hr : 0 < r,
      ∀ u : MetricUnit (hermitianMetric J α hs ht), u.val.proj ∈ tsupport (A.partition p) →
      |unitEvaluation J (hermitianMetric J α hs ht)
        (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
        ((scalarDifferential_smooth (concentrationPatch_smooth A J α hs ht E μ p hr)).wedgeOne θ.property) u| ≤
      C*(localConcentration A J α hs ht E μ p r (unitChartBase J α hs ht p.val u)+
        A.partition p u.val.proj *
          (|fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartFirst J α hs ht p.val u)|+
           |fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)|)) := by
  obtain ⟨B,hB,hθ⟩ := concentration_theta_bound A J α ht E p θ
  obtain ⟨D,hD,hd⟩ := concentration_partition_derivative_bound A J α ht E p
  obtain ⟨_,M,_,hM,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  refine ⟨M*B*(2*D+1),by positivity,fun μ _ r hr u hx => ?_⟩
  have hu := unitChartPlane J α hs ht p.val u (A.subordinate p hx)
  have hz := (E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)
  have htgt := (E p).concentrationCompact_target hz
  have huK : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
    ⟨_,hz,(extChartAt Model p.val).left_inv (A.subordinate p hx)⟩
  let z := unitChartBase J α hs ht p.val u
  let f := localConcentration A J α hs ht E μ p r
  let χ := A.partition p u.val.proj
  let d := fderiv ℝ (coordinatePartition A p) z
  let l := fderiv ℝ f z
  have hf : 0 ≤ f z := localConcentration_nonneg A J α hs ht E μ p r z
  have hχ : 0 ≤ χ := A.partition.nonneg _ _
  have hw : |(f z • d+χ • l) (unitChartFirst J α hs ht p.val u)| ≤ f z*D+χ*|l (unitChartFirst J α hs ht p.val u)| := by
    have hh : |d (unitChartFirst J α hs ht p.val u)| ≤ D := by
      have h := d.le_opNorm (unitChartFirst J α hs ht p.val u)
      rw [hu.1,mul_one] at h
      exact h.trans (hd z hz)
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
    exact (abs_add_le _ _).trans (by rw [abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg hχ]; gcongr)
  have hv : |(f z • d+χ • l) (unitChartSecond J α hs ht p.val u)| ≤ f z*D+χ*|l (unitChartSecond J α hs ht p.val u)| := by
    have hh : |d (unitChartSecond J α hs ht p.val u)| ≤ D := by
      have h := d.le_opNorm (unitChartSecond J α hs ht p.val u)
      rw [hu.2.1,mul_one] at h
      exact h.trans (hd z hz)
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
    exact (abs_add_le _ _).trans (by rw [abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg hχ]; gcongr)
  have heval := unitChartArea_eval J α hs ht p.val
    (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
    ((scalarDifferential_smooth (concentrationPatch_smooth A J α hs ht E μ p hr)).wedgeOne θ.property) u (A.subordinate p hx)
  change eval _ u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) = _ at heval
  change |eval _ u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤ _
  rw [heval]
  dsimp only [unitChartBase]
  rw [concentrationPatch_wedge_chart A J α hs ht E μ p hr θ.val htgt,
    coordinatePartition_apply A p (A.subordinate p hx),abs_mul,abs_of_pos hu.2.2.2]
  have hh := ExteriorForms.scalar_wedge_unit (f z • d+χ • l)
    (ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z)
    (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) hu.1 hu.2.1
  have hh' : |ExteriorForms.wedgeOne (f z • d+χ • l)
      (ManifoldForms.pullback θ.val (extChartAt Model p.val).symm z)
      ![unitChartFirst J α hs ht p.val u,unitChartSecond J α hs ht p.val u]| ≤
      B*(2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|)) := by
    exact hh.trans ((mul_le_mul (hθ z hz) (add_le_add hw hv) (by positivity) hB).trans_eq (by ring))
  have hb := mul_le_mul (harea u huK).2 hh' (abs_nonneg _) hM.le
  have hn : 0 ≤ χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|) := by positivity
  have hbb : 0 ≤ M*B := by positivity
  have he : 2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|) ≤
      (2*D+1)*(f z+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|)) := by nlinarith
  calc
    _ ≤ M*(B*(2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|))) := hb
    _ = (M*B)*(2*D*(f z)+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|)) := by ring
    _ ≤ (M*B)*((2*D+1)*(f z+χ*(|l (unitChartFirst J α hs ht p.val u)|+|l (unitChartSecond J α hs ht p.val u)|))) := mul_le_mul_of_nonneg_left he hbb
    _ = _ := by dsimp only [f,z,l,χ,unitChartBase] <;> ring

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
variable {V : Type*} [NormedAddCommGroup V]

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma physicalQError_nonneg (q : X → V) {L r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ physicalQError A J α hs ht q L r x := by
  apply integral_nonneg
  intro y
  exact div_nonneg (mul_nonneg (norm_nonneg _) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)

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

lemma physicalQError_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (q : X → V) (hq : Integrable q (geometricVolume A J α)) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) => physicalQError A J α hs ht q L r u.val.proj) μ := by
  let := geometricVolume_finite A J α hs ht
  exact (physicalQError_product_integrable A J α hs ht μ q hq hL hr).integral_prod_left

lemma physicalQError_integral
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (q : X → V) (hq : Integrable q (geometricVolume A J α)) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) :
    (∫ u, physicalQError A J α hs ht q L r u.val.proj ∂μ) =
      ∫ y, ‖q y‖*physicalGradientMass J α hs ht μ L r y ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  unfold physicalQError
  rw [integral_integral_swap (physicalQError_product_integrable A J α hs ht μ q hq hL hr)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  simp_rw [physicalProfile_symm J α hs ht (L*r) _ y]
  rw [integral_div,integral_const_mul]
  simp only [physicalGradientMass,physicalProfileMass,mul_div_assoc]

lemma physicalQError_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (q : X → V) (hq : MemLp q 2 (geometricVolume A J α)) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun r : ℝ => ∫ u, physicalQError A J α hs ht q L r u.val.proj ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let := geometricVolume_finite A J α hs ht
  apply (physicalGradientMass_L2_limit A J α hs ht μ hann q hq hL).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (physicalQError_integral A J α hs ht μ q (hq.integrable (by norm_num)) hL hr).symm
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationVariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [T2Space X] [CompactSpace X] in
lemma variationDensity_nonneg (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ variationDensity A J α hs ht E p r uv := by
  apply mul_nonneg (A.partition.nonneg _ _)
  apply indicator_nonneg _ uv.1
  intro u _
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.PlaneVariation
open Set
open scoped RealInnerProductSpace
lemma continuousOn_variation {Y V : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f g : Y → V} {S : Set Y} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun uv : Y × Y => f uv.2-skew (f uv.1) (g uv.1) (g uv.2)) (S ×ˢ S) := by
  have hf1 : ContinuousOn (fun uv : Y × Y => f uv.1) (S ×ˢ S) := hf.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hf2 : ContinuousOn (fun uv : Y × Y => f uv.2) (S ×ˢ S) := hf.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg1 : ContinuousOn (fun uv : Y × Y => g uv.1) (S ×ˢ S) := hg.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hg2 : ContinuousOn (fun uv : Y × Y => g uv.2) (S ×ˢ S) := hg.comp continuous_snd.continuousOn (fun _ h => h.2)
  exact hf2.sub (((hg1.inner hg2).smul hf1).sub ((hf1.inner hg2).smul hg1))
end TamingCompatibility.PlaneVariation
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
omit [T2Space X] [CompactSpace X] [SecondCountableTopology X] in
lemma variationDensity_eq_indicator (p : A.centers) (r : ℝ) :
    variationDensity A J α hs ht E p r =
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)).indicator
        (variationRaw A J α hs ht E p r) := by
  funext uv
  by_cases hu : uv.1 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · by_cases hv : uv.2 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
    · simp only [variationDensity,indicator_of_mem hu,indicator_of_mem (show uv ∈ _ ×ˢ _ from ⟨hu,hv⟩),variationRaw]
    · have hz : A.partition p uv.2.val.proj = 0 := by
        by_contra hn
        have hc := partition_center_ball A J α ht E hE p (subset_tsupport _ hn)
        have hsrc := (E p).source_subset (hE p (subset_tsupport _ hn))
        exact hv ⟨_,(E p).concentrationCompact_center hc,(extChartAt Model p.val).left_inv hsrc⟩
      simp only [variationDensity,indicator_of_mem hu,hz,zero_mul,
        indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hv h.2)]
  · simp only [variationDensity,indicator_of_notMem hu,mul_zero,
      indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hu h.1)]

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma variationVector_continuousOn (p : A.centers) :
    ContinuousOn (variationVector A J α hs ht p)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  exact PlaneVariation.continuousOn_variation
    (unitChartFirst_continuousOn J α hs ht p.val (E p).concentrationCompact_target)
    (unitChartSecond_continuousOn J α hs ht p.val (E p).concentrationCompact_target)

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma variationRaw_continuousOn (p : A.centers) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (variationRaw A J α hs ht E p r)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  let S := unitChartDomain J α hs ht p.val (E p).concentrationCompact
  have hb := unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target
  have hz : ContinuousOn (fun uv : UnitPair J α hs ht =>
      unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) (S ×ˢ S) :=
    (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hd := ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn hz
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => unitChartArea J α hs ht p.val uv.1) (S ×ˢ S) := (unitChartArea_continuousOn J α hs ht p.val (E p).concentrationCompact_target).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hp : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.2.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn
  exact hp.mul (ha.mul (hd.clm_apply (variationVector_continuousOn A J α hs ht E p)).abs)

include hE in
lemma variationDensity_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) {r : ℝ} (hr : 0 < r) :
    Integrable (variationDensity A J α hs ht E p r) (μ.prod μ) := by
  classical
  let S := (unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)
  have hc := unitChartDomain_closed J α hs ht p.val (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hS : _root_.IsClosed S := hc.prod hc
  have hf := variationRaw_continuousOn A J α hs ht E p hr
  have hm := hf.measurable_piecewise
    (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) Sᶜ) hS.measurableSet
  have hm' : Measurable (variationDensity A J α hs ht E p r) := by
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext uv
    rw [variationDensity_eq_indicator A J α hs ht E hE p r]
    by_cases huv : uv ∈ S <;> simp [Set.indicator, Set.piecewise, S] at huv ⊢
  obtain ⟨C,hC⟩ := hS.isCompact.exists_bound_of_continuousOn hf
  apply (integrable_const (max C 0 : ℝ)).mono' hm'.aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [variationDensity_eq_indicator A J α hs ht E hE p r]
  by_cases huv : uv ∈ S
  · rw [indicator_of_mem huv]
    exact (hC uv huv).trans (le_max_left _ _)
  · rw [indicator_of_notMem huv,norm_zero]
    exact le_max_right _ _
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondPlaneVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [T2Space X] [CompactSpace X] in
lemma secondVariationDensity_nonneg (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ secondVariationDensity A J α hs ht E p r uv := by
  apply mul_nonneg (A.partition.nonneg _ _)
  apply indicator_nonneg _ uv.1
  intro u _
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondVariationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.PlaneVariation
open Set
open scoped RealInnerProductSpace
lemma continuousOn_secondVariation {Y V : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f g : Y → V} {S : Set Y} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun uv : Y × Y => g uv.2-skew (f uv.1) (g uv.1) (-f uv.2)) (S ×ˢ S) := by
  have hf1 : ContinuousOn (fun uv : Y × Y => f uv.1) (S ×ˢ S) := hf.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hf2 : ContinuousOn (fun uv : Y × Y => f uv.2) (S ×ˢ S) := hf.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg1 : ContinuousOn (fun uv : Y × Y => g uv.1) (S ×ˢ S) := hg.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hg2 : ContinuousOn (fun uv : Y × Y => g uv.2) (S ×ˢ S) := hg.comp continuous_snd.continuousOn (fun _ h => h.2)
  exact hg2.sub (((hg1.inner hf2.neg).smul hf1).sub ((hf1.inner hf2.neg).smul hg1))
end TamingCompatibility.PlaneVariation
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
omit [T2Space X] [CompactSpace X] [SecondCountableTopology X] in
lemma secondVariationDensity_eq_indicator (p : A.centers) (r : ℝ) :
    secondVariationDensity A J α hs ht E p r =
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)).indicator
        (secondVariationRaw A J α hs ht E p r) := by
  funext uv
  by_cases hu : uv.1 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · by_cases hv : uv.2 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
    · simp only [secondVariationDensity,indicator_of_mem hu,indicator_of_mem (show uv ∈ _ ×ˢ _ from ⟨hu,hv⟩),secondVariationRaw]
    · have hz : A.partition p uv.2.val.proj = 0 := by
        by_contra hn
        have hc := partition_center_ball A J α ht E hE p (subset_tsupport _ hn)
        have hsrc := (E p).source_subset (hE p (subset_tsupport _ hn))
        exact hv ⟨_,(E p).concentrationCompact_center hc,(extChartAt Model p.val).left_inv hsrc⟩
      simp only [secondVariationDensity,indicator_of_mem hu,hz,zero_mul,
        indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hv h.2)]
  · simp only [secondVariationDensity,indicator_of_notMem hu,mul_zero,
      indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hu h.1)]

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma secondVariationVector_continuousOn (p : A.centers) :
    ContinuousOn (secondVariationVector A J α hs ht p)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  exact PlaneVariation.continuousOn_secondVariation
    (unitChartFirst_continuousOn J α hs ht p.val (E p).concentrationCompact_target)
    (unitChartSecond_continuousOn J α hs ht p.val (E p).concentrationCompact_target)

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma secondVariationRaw_continuousOn (p : A.centers) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (secondVariationRaw A J α hs ht E p r)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  let S := unitChartDomain J α hs ht p.val (E p).concentrationCompact
  have hb := unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target
  have hz : ContinuousOn (fun uv : UnitPair J α hs ht =>
      unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) (S ×ˢ S) :=
    (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hd := ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn hz
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => unitChartArea J α hs ht p.val uv.1) (S ×ˢ S) := (unitChartArea_continuousOn J α hs ht p.val (E p).concentrationCompact_target).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hp : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.2.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn
  exact hp.mul (ha.mul (hd.clm_apply (secondVariationVector_continuousOn A J α hs ht E p)).abs)

include hE in
lemma secondVariationDensity_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) {r : ℝ} (hr : 0 < r) :
    Integrable (secondVariationDensity A J α hs ht E p r) (μ.prod μ) := by
  classical
  let S := (unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)
  have hc := unitChartDomain_closed J α hs ht p.val (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hS : _root_.IsClosed S := hc.prod hc
  have hf := secondVariationRaw_continuousOn A J α hs ht E p hr
  have hm := hf.measurable_piecewise
    (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) Sᶜ) hS.measurableSet
  have hm' : Measurable (secondVariationDensity A J α hs ht E p r) := by
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext uv
    rw [secondVariationDensity_eq_indicator A J α hs ht E hE p r]
    by_cases huv : uv ∈ S <;> simp [Set.indicator, Set.piecewise, S] at huv ⊢
  obtain ⟨C,hC⟩ := hS.isCompact.exists_bound_of_continuousOn hf
  apply (integrable_const (max C 0 : ℝ)).mono' hm'.aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [secondVariationDensity_eq_indicator A J α hs ht E hE p r]
  by_cases huv : uv ∈ S
  · rw [indicator_of_mem huv]
    exact (hC uv huv).trans (le_max_left _ _)
  · rw [indicator_of_notMem huv,norm_zero]
    exact le_max_right _ _
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
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE hD hG in
lemma concentrationPatch_error_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (p : A.centers) :
    ∃ e : ℝ → MetricUnit (hermitianMetric J α hs ht) → ℝ,
      (∀ r, 0 < r → ∀ u, 0 ≤ e r u) ∧
      (∀ r, 0 < r → Integrable (e r) μ) ∧
      Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤
        C*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
  let := geometricVolume_finite A J α hs ht
  let q := l2Coefficients A J α hs ht E hE Q
  have hq : Integrable q (geometricVolume A J α) := (Lp.memLp q).integrable (by norm_num)
  obtain ⟨a,b,ha,hb,hcomp⟩ := localConcentration_global_compare A J α hs ht E hE μ p
  obtain ⟨B,C,L,hB,hC,hL,hplane⟩ := concentration_plane_estimate A J α hs ht E hE μ Q hT p
  let v₁ := fun r u => ∫ v, variationDensity A J α hs ht E p r (v,u) ∂μ
  let v₂ := fun r u => ∫ v, secondVariationDensity A J α hs ht E p r (v,u) ∂μ
  let e := fun r u => B*physicalQError A J α hs ht q L r u.val.proj+(b+C)*r^4+v₁ r u+v₂ r u
  have hv₁ (r) (u) : 0 ≤ v₁ r u := integral_nonneg (fun v => variationDensity_nonneg A J α hs ht E p r (v,u))
  have hv₂ (r) (u) : 0 ≤ v₂ r u := integral_nonneg (fun v => secondVariationDensity_nonneg A J α hs ht E p r (v,u))
  have he (r) (hr : 0 < r) (u) : 0 ≤ e r u := by
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hB (physicalQError_nonneg A J α hs ht q hr _))
      (mul_nonneg (add_nonneg hb hC) (by positivity))) (hv₁ r u)) (hv₂ r u)
  have hi₁ (r) (hr : 0 < r) : Integrable (v₁ r) μ :=
    (variationDensity_integrable A J α hs ht E hE μ p hr).integral_prod_right
  have hi₂ (r) (hr : 0 < r) : Integrable (v₂ r) μ :=
    (secondVariationDensity_integrable A J α hs ht E hE μ p hr).integral_prod_right
  have hqi (r) (hr : 0 < r) := physicalQError_integrable A J α hs ht μ q hq hL hr
  have hei (r) (hr : 0 < r) : Integrable (e r) μ :=
    (((hqi r hr).const_mul B).add (integrable_const ((b+C)*r^4))).add (hi₁ r hr) |>.add (hi₂ r hr)
  have hiEq (r) (hr : 0 < r) : (∫ u, e r u ∂μ) =
      B*(∫ u, physicalQError A J α hs ht q L r u.val.proj ∂μ)+(b+C)*r^4+
      (∫ uv, variationDensity A J α hs ht E p r uv ∂μ.prod μ)+
      (∫ uv, secondVariationDensity A J α hs ht E p r uv ∂μ.prod μ) := by
    erw [show e r = (fun u => B*physicalQError A J α hs ht q L r u.val.proj+(b+C)*r^4+v₁ r u+v₂ r u) from rfl,
      integral_add ((((hqi r hr).const_mul B).add (integrable_const ((b+C)*r^4))).add (hi₁ r hr)) (hi₂ r hr),
      integral_add (((hqi r hr).const_mul B).add (integrable_const ((b+C)*r^4))) (hi₁ r hr),
      integral_add ((hqi r hr).const_mul B) (integrable_const ((b+C)*r^4)),integral_const_mul,
      integral_const,probReal_univ,one_smul]
    have h1 : (∫ u, v₁ r u ∂μ) = ∫ uv, variationDensity A J α hs ht E p r uv ∂μ.prod μ :=
      (integral_prod_symm _ (variationDensity_integrable A J α hs ht E hE μ p hr)).symm
    have h2 : (∫ u, v₂ r u ∂μ) = ∫ uv, secondVariationDensity A J α hs ht E p r uv ∂μ.prod μ :=
      (integral_prod_symm _ (secondVariationDensity_integrable A J α hs ht E hE μ p hr)).symm
    rw [h1,h2]
  have he0 : Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h0 := physicalQError_limit A J α hs ht μ hann q (Lp.memLp q) hL
    have h1 := separating_current_variation_limit A J α hs ht E hE D hD G hG μ hann p
    have h2 := separating_current_second_variation_limit A J α hs ht E hE D hD G hG μ hann p
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have htend := (((h0.const_mul B).add ((hr.pow 4).const_mul (b+C))).add h1).add h2
    simp only [zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,add_zero] at htend
    apply htend.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hiEq r hr).symm
  refine ⟨e,he,hei,he0,fun θ => ?_⟩
  obtain ⟨K,hK,hbound⟩ := concentrationPatch_tangential_bound A J α hs ht E hE p θ
  refine ⟨K*(a+1),by positivity,fun r hr u => ?_⟩
  by_cases hx : u.val.proj ∈ tsupport (A.partition p)
  · have hh := hbound μ r hr u hx
    change |eval _ u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤ _ at hh
    have hp := hplane r hr u
    have hb' := hcomp u.val.proj hx r hr
    have hF := globalConcentration_nonneg A J α hs ht E μ r u.val.proj
    have hsum : localConcentration A J α hs ht E μ p r (unitChartBase J α hs ht p.val u)+
        A.partition p u.val.proj *
          (|fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartFirst J α hs ht p.val u)|+
           |fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)|) ≤
        (a+1)*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
      have hen := he r hr u
      dsimp only [e,v₁,v₂,unitChartBase,q] at hp hb' hen ⊢
      nlinarith
    exact hh.trans ((mul_le_mul_of_nonneg_left hsum hK).trans_eq (by ring))
  · unfold eval
    rw [concentrationPatch_wedge_zero_off A J α hs ht E μ p r θ.val hx]
    change |(0 : ℝ)| ≤ _
    rw [abs_zero]
    exact mul_nonneg (by positivity) (add_nonneg (globalConcentration_nonneg A J α hs ht E μ r _) (he r hr u))
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

include hE hD hG in
lemma globalConcentration_current_control_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    ∃ e : ℝ → MetricUnit (hermitianMetric J α hs ht) → ℝ,
      (∀ r, 0 < r → ∀ u, 0 ≤ e r u) ∧
      (∀ r, 0 < r → Integrable (e r) μ) ∧
      Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤
        C*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
  classical
  choose e he hi h0 hb using fun p => concentrationPatch_error_control A J α hs ht E hE D hD G hG μ hann Q hT p
  let err := fun r u => ∑ p : A.centers, e p r u
  have hn (r) (hr : 0 < r) (u) : 0 ≤ err r u := Finset.sum_nonneg (fun p _ => he p r hr u)
  have hin (r) (hr : 0 < r) : Integrable (err r) μ := integrable_finsetSum _ (fun p _ => hi p r hr)
  have hlim : Tendsto (fun r => ∫ u, err r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun p _ => h0 p)
    simp only [Finset.sum_const_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (integral_finsetSum _ (fun p _ => hi p r hr)).symm
  refine ⟨err,hn,hin,hlim,fun θ => ?_⟩
  choose C hC hbound using fun p => hb p θ
  refine ⟨∑ p, C p,Finset.sum_nonneg (fun p _ => hC p),fun r hr u => ?_⟩
  rw [globalConcentration_wedge A J α hs ht E μ hr θ.val]
  have heval : eval (∑ p : A.centers, ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
      u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) =
      ∑ p : A.centers, eval (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
    simp only [eval,Finset.sum_apply]
    erw [ContinuousAlternatingMap.sum_apply]
  rw [heval,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _
  have hep : e p r u ≤ err r u := Finset.single_le_sum (fun i _ => he i r hr u) (Finset.mem_univ p)
  exact (hbound p r hr u).trans (mul_le_mul_of_nonneg_left (add_le_add_right hep _) (hC p))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control_oai.{u_1}
