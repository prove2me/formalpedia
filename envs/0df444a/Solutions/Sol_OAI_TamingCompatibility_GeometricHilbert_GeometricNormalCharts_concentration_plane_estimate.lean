-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:08.104568+00:00
-- url     : https://prove2.me/submissions/94e94d03-1227-467b-9011-6a975f4be080

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc020
import Definitions.Def_OAIQ239Tc021

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
attribute [local instance] unitMeasurable unitBorel unitT2

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

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]

lemma pullback_exteriorDerivative_chartLift {k : ℕ} (p : X)
    {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hs : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hβ : tsupport β ⊆ (extChartAt Model p).target)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (exteriorDerivative (chartLift p β)) (extChartAt Model p).symm z = extDeriv β z := by
  rw [pullback_exteriorDerivative _ (chartLift_smooth p hs hc hβ)
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hz,
    extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
  exact pullback_chartLift p β hy

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.Concentration
open ContinuousAlternatingMap ExteriorForms
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma testOne_deriv {h : V → ℝ} (hh : Differentiable ℝ h) (v y a b : V) :
    extDeriv (testOne h v) y ![a,b] =
      (fderiv ℝ h y a)*⟪v,b⟫-(fderiv ℝ h y b)*⟪v,a⟫ := by
  unfold testOne
  rw [extDeriv_variable_smul (hh y) (differentiableAt_const _)]
  have hz : extDeriv (fun _ : V => ofSubsingletonLIE (0 : Fin 1) (innerSL ℝ v)) y = 0 := by
    rw [extDeriv,fderiv_fun_const]
    change alternatizeUncurryFinCLM ℝ V ℝ 0 = 0
    exact map_zero _
  rw [hz,smul_zero,zero_add,wedgeOne_apply_two]
  rfl

lemma testOne_skew {h : V → ℝ} (hh : Differentiable ℝ h) (v y a b : V) :
    extDeriv (testOne h v) y ![a,b] =
      fderiv ℝ h y (⟪v,b⟫ • a - ⟪v,a⟫ • b) := by
  rw [testOne_deriv hh,map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  ring
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
attribute [local instance] unitMeasurable unitBorel unitT2 

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
attribute [local instance] unitMeasurable unitBorel unitT2

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

omit [CompactSpace X] [T2Space X] in
lemma unitChartSkew_continuousOn (p : X) (v : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (fun u => skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v)
      (unitChartDomain J α hs ht p K) := by
  let S := unitChartDomain J α hs ht p K
  let f := unitChartFirst J α hs ht p
  let g := unitChartSecond J α hs ht p
  have hf : ContinuousOn f S := unitChartFirst_continuousOn J α hs ht p hKT
  have hg : ContinuousOn g S := unitChartSecond_continuousOn J α hs ht p hKT
  have hi : ContinuousOn (fun u => inner ℝ (g u) v) S := hg.inner continuousOn_const
  have hj : ContinuousOn (fun u => inner ℝ (f u) v) S := hf.inner continuousOn_const
  exact (hi.smul hf).sub (hj.smul hg)

end TamingCompatibility.GeometricHilbert.Hermitian

namespace TamingCompatibility.Concentration
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma reflected_derivative {k : V → ℝ} (hk : Differentiable ℝ k) (b y w : V) :
    fderiv ℝ (fun y => k (b-y)) y w = -fderiv ℝ k (b-y) w := by
  have hh := (hk (b-y)).hasFDerivAt.comp y ((hasFDerivAt_const b y).sub (hasFDerivAt_id y))
  change HasFDerivAt (fun y => k (b-y)) _ y at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

end TamingCompatibility.Concentration

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

attribute [local instance] unitMeasurable unitBorel unitT2

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneTest
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
attribute [local instance] unitMeasurable unitBorel unitT2

omit [CompactSpace X] in
lemma planeCurrentTest_closed (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target) :
    IsClosed (planeCurrentTest p h v hh hc hT).val :=
  (chartLift_smooth p (testOne_smooth hh v) (testOne_compact hc v)
    ((testOne_support h v).trans hT)).closed_exteriorDerivative

omit [CompactSpace X] in
lemma planeCurrentTest_zero_off (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target)
    {K : Set Space} (hsK : tsupport h ⊆ K) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' K) :
    (planeCurrentTest p h v hh hc hT).val x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  have hxc : x ∉ liftSupport p (testOne h v) := by
    rintro ⟨z,hz,hzx⟩
    exact hx ⟨z,hsK (testOne_support h v hz),hzx⟩
  filter_upwards [(liftSupport_compact p (testOne_compact hc v)
    ((testOne_support h v).trans hT)).isClosed.isOpen_compl.mem_nhds hxc] with y hy
  exact chartLift_zero_off p (testOne h v) hy

omit [CompactSpace X] in
lemma planeCurrentTest_eval (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    unitEvaluation J (hermitianMetric J α hs ht)
      (planeCurrentTest p h v hh hc hT).val (planeCurrentTest p h v hh hc hT).property u =
      unitChartArea J α hs ht p u *
        fderiv ℝ h (unitChartBase J α hs ht p u)
          (skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v) := by
  have he := unitChartArea_eval J α hs ht p
    (planeCurrentTest p h v hh hc hT).val
    (show IsSmooth (planeCurrentTest p h v hh hc hT).val from
      (planeCurrentTest p h v hh hc hT).property) u hu
  apply he.trans
  change unitChartArea J α hs ht p u *
    ManifoldForms.pullback (exteriorDerivative (chartLift p (testOne h v)))
      (extChartAt Model p).symm (unitChartBase J α hs ht p u) _ = _
  simp only [unitChartBase]
  rw [pullback_exteriorDerivative_chartLift p (testOne_smooth hh v) (testOne_compact hc v)
      ((testOne_support h v).trans hT) ((extChartAt Model p).map_source hu),
    testOne_skew (hh.differentiable (by simp))]
  simp only [skew,real_inner_comm]

lemma planeCurrentTest_current (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    {K : Set Space} (hKT : K ⊆ (extChartAt Model p).target) (hsK : tsupport h ⊆ K)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    unitMeasureCurrent J (hermitianMetric J α hs ht) μ (planeCurrentTest p h v hh hc (hsK.trans hKT)) =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u *
          fderiv ℝ h (unitChartBase J α hs ht p u)
            (skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v)) u ∂μ := by
  apply integral_congr_ae
  apply ae_of_all
  intro u
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · rw [indicator_of_mem hu]
    exact planeCurrentTest_eval J α hs ht p h v hh hc (hsK.trans hKT) u
      (unitChart_mem J α hs ht p hKT hu).1
  · rw [indicator_of_notMem hu]
    change ((planeCurrentTest p h v hh hc (hsK.trans hKT)).val u.val.proj) _ = 0
    rw [planeCurrentTest_zero_off p h v hh hc (hsK.trans hKT) hsK hu]
    rfl
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneFirstVariation
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
attribute [local instance] unitMeasurable unitBorel unitT2

lemma planeConvolution_first_variation (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (b w v : Space) (hsK : tsupport (fun y => k (b-y)) ⊆ K) :
    fderiv ℝ (planeConvolution J α hs ht p K μ k) b w +
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ
        (planeCurrentTest p (fun y => k (b-y)) v
          (reflected_smooth k hk b) (reflected_compact k hc b) (hsK.trans hKT)) =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u *
          fderiv ℝ k (b-unitChartBase J α hs ht p u)
            (w-skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v)) u ∂μ := by
  let S := unitChartDomain J α hs ht p K
  have hb : ContinuousOn (fun u => b-unitChartBase J α hs ht p u) S :=
    continuousOn_const.sub (unitChartBase_continuousOn J α hs ht p hKT)
  have hd : ContinuousOn (fun u => fderiv ℝ k (b-unitChartBase J α hs ht p u)) S :=
    (hk.continuous_fderiv (by simp)).comp_continuousOn hb
  have hw := planeWeighted_integrable J α hs ht p hK hKT μ
    (fun u => fderiv ℝ k (b-unitChartBase J α hs ht p u) w) (hd.clm_apply continuousOn_const)
  have hv := planeWeighted_integrable J α hs ht p hK hKT μ
    (fun u => -fderiv ℝ k (b-unitChartBase J α hs ht p u)
      (skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v))
    ((hd.clm_apply (unitChartSkew_continuousOn J α hs ht p v hKT)).neg)
  simp only [smul_eq_mul] at hw hv
  rw [planeConvolution_deriv J α hs ht p hK hKT μ k hk hc,
    planeCurrentTest_current J α hs ht p _ v _ _ hKT hsK μ]
  simp_rw [reflected_derivative (hk.differentiable (by simp))]
  rw [← integral_add hw hv]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  by_cases hu : u ∈ S
  · dsimp only [S] at hu
    simp only [indicator_of_mem hu,map_sub]
    ring
  · dsimp only [S] at hu
    simp only [indicator_of_notMem hu,add_zero]
end TamingCompatibility.GeometricHilbert.Hermitian

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
attribute [local instance] unitMeasurable unitBorel unitT2

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

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactProfilePoint
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
lemma compact_chart_profile_bound_points (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : X,
      x ∈ (extChartAt Model p).source → y ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → extChartAt Model p y ∈ K → ∀ r : ℝ, 0 < r →
      ((1+‖extChartAt Model p x-extChartAt Model p y‖/r)⁻¹)^6 ≤
        physicalProfile J α hs ht (L*r) x y := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨L₀,hL₀⟩ := chartInverse_compact_lipschitz J α hs ht p K hK hKT
  let L : ℝ := (L₀:ℝ)+1
  have hL : 0 < L := by dsimp [L] <;> positivity
  refine ⟨L,hL,fun x y hx hy hxK hyK r hr => ?_⟩
  have hphys := hL₀.dist_le_mul _ hxK _ hyK
  change dist ((extChartAt Model p).symm (extChartAt Model p x))
    ((extChartAt Model p).symm (extChartAt Model p y)) ≤ _ at hphys
  rw [(extChartAt Model p).left_inv hx,(extChartAt Model p).left_inv hy,dist_eq_norm] at hphys
  have htransport : dist x y ≤ L*‖extChartAt Model p x-extChartAt Model p y‖ :=
    hphys.trans (mul_le_mul_of_nonneg_right (by dsimp [L] <;> linarith) (norm_nonneg _))
  have hdiv : dist x y/(L*r) ≤ ‖extChartAt Model p x-extChartAt Model p y‖/r := by
    apply (div_le_iff₀ (mul_pos hL hr)).mpr
    calc
      _ ≤ L*‖extChartAt Model p x-extChartAt Model p y‖ := htransport
      _ = _ := by field_simp
  change _ ≤ ((1+dist x y/(L*r))⁻¹)^6
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 6
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory
open scoped RealInnerProductSpace
namespace TamingCompatibility.GeometricHilbert
variable {V E X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace X]
  {μ : Measure X}

variable [CompleteSpace E]

lemma isometryFromCompletion_coe (f : V →ₗᵢ[ℝ] E) (v : V) :
    isometryFromCompletion f (v : UniformSpace.Completion V) = f v :=
  f.toContinuousLinearMap.fromCompletion_apply_coe v

end TamingCompatibility.GeometricHilbert

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization HodgeFrame _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma l2Coefficients_smooth (a : PreL2 A J α hs ht true) :
    ∀ᵐ x ∂geometricVolume A J α,
      l2Coefficients A J α hs ht E hE (smoothL2 A J α hs ht true a) x =
        normalizedFrameEncode A J α ht E x (a.val x) := by
  change ∀ᵐ x ∂geometricVolume A J α,
    isometryFromCompletion (lpEncodeIsometry (smoothFrameEncode A J α hs ht E)
      (smoothFrameEncode_memLp A J α hs ht E hE)
      (smoothFrameEncode_inner_integral A J α hs ht E hE))
        (a : UniformSpace.Completion (PreL2 A J α hs ht true)) x = _
  rw [isometryFromCompletion_coe]
  exact (smoothFrameEncode_memLp A J α hs ht E hE a).coeFn_toLp

lemma l2Coefficients_pairing (Q : L2 A J α hs ht true) (a : PreL2 A J α hs ht true) :
    ⟪Q,smoothL2 A J α hs ht true a⟫ =
      ∫ x, ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (a.val x)⟫ ∂geometricVolume A J α := by
  rw [← (l2Coefficients A J α hs ht E hE).inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Coefficients_smooth A J α hs ht E hE a] with x hx
  rw [hx]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_TestNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.Concentration
open ContinuousAlternatingMap ExteriorForms
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma testOne_deriv_norm {h : V → ℝ} (hh : Differentiable ℝ h) (v y : V) :
    ‖extDeriv (testOne h v) y‖ ≤ 2*‖fderiv ℝ h y‖*‖v‖ := by
  apply ContinuousAlternatingMap.opNorm_le_bound _ (by positivity)
  intro m
  have he : ![m 0,m 1] = m := by ext i; fin_cases i <;> rfl
  rw [← he,testOne_deriv hh,Real.norm_eq_abs,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ ≤ |fderiv ℝ h y (m 0)*⟪v,m 1⟫|+|fderiv ℝ h y (m 1)*⟪v,m 0⟫| := by simpa only [Real.norm_eq_abs] using norm_sub_le (fderiv ℝ h y (m 0)*⟪v,m 1⟫) (fderiv ℝ h y (m 1)*⟪v,m 0⟫)
    _ = |fderiv ℝ h y (m 0)| *|⟪v,m 1⟫|+|fderiv ℝ h y (m 1)| *|⟪v,m 0⟫| := by rw [abs_mul,abs_mul]
    _ ≤ (‖fderiv ℝ h y‖*‖m 0‖)*(‖v‖*‖m 1‖)+
        (‖fderiv ℝ h y‖*‖m 1‖)*(‖v‖*‖m 0‖) := by
      apply add_le_add <;> apply mul_le_mul
      · exact (fderiv ℝ h y).le_opNorm (m 0)
      · exact abs_real_inner_le_norm _ _
      · positivity
      · positivity
      · exact (fderiv ℝ h y).le_opNorm (m 1)
      · exact abs_real_inner_le_norm _ _
      · positivity
      · positivity
    _ = _ := by ring
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneTestCoefficient
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
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [CompactSpace X] in
lemma planeCurrentTest_coefficient_bound (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space → ℝ, ∀ v : Space,
      ∀ hh : ContDiff ℝ ∞ h, ∀ hc : HasCompactSupport h,
      ∀ hK : tsupport h ⊆ (E p).concentrationCompact, ∀ x : X,
      ‖normalizedFrameEncode A J α ht E x
        ((planeCurrentTest p.val h v hh hc (hK.trans (E p).concentrationCompact_target)).val x)‖ ≤
        C*‖fderiv ℝ h (extChartAt Model p.val x)‖*‖v‖ := by
  obtain ⟨C,hC,hbound⟩ := normalizedFrameEncode_chart_bound A J α ht E hE p
  refine ⟨2*C,by positivity,fun h v hh hc hK x => ?_⟩
  by_cases hx : x ∈ (extChartAt Model p.val).symm '' (E p).concentrationCompact
  · obtain ⟨y,hy,rfl⟩ := hx
    have htgt := (E p).concentrationCompact_target hy
    have hb := hbound (planeCurrentTest p.val h v hh hc (hK.trans (E p).concentrationCompact_target)).val y hy
    change ‖normalizedFrameEncode A J α ht E _ _‖ ≤ C*‖ManifoldForms.pullback
      (exteriorDerivative (chartLift p.val (testOne h v))) (extChartAt Model p.val).symm y‖ at hb
    rw [pullback_exteriorDerivative_chartLift p.val (testOne_smooth hh v) (testOne_compact hc v)
      ((testOne_support h v).trans (hK.trans (E p).concentrationCompact_target)) htgt] at hb
    rw [(extChartAt Model p.val).right_inv htgt]
    exact hb.trans ((mul_le_mul_of_nonneg_left (testOne_deriv_norm
      (hh.differentiable (by simp)) v y) hC).trans_eq (by ring))
  · rw [planeCurrentTest_zero_off p.val h v hh hc (hK.trans (E p).concentrationCompact_target) hK hx]
    change ‖normalizedFrameEncode A J α ht E x (0 : MetricForms.Form Space 2)‖ ≤ _
    rw [map_zero,norm_zero]
    positivity

lemma reflected_fderiv_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : V → ℝ} (hh : Differentiable ℝ h) (b y : V) :
    ‖fderiv ℝ (fun z => h (b-z)) y‖ = ‖fderiv ℝ h (b-y)‖ := by
  have he : fderiv ℝ (fun z => h (b-z)) y = -fderiv ℝ h (b-y) := by
    ext w
    exact reflected_derivative hh b y w
  rw [he,norm_neg]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationTest
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
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [ConnectedSpace X] in
lemma concentrationTest_closed (p : A.centers) {r : ℝ} (hr : 0 < r)
    (x : X) (hx : x ∈ tsupport (A.partition p)) (v : Space) :
    IsClosed (concentrationTest A J α ht E hE p r hr x hx v).val :=
  planeCurrentTest_closed _ _ _ _ _ _

include hE in
lemma concentrationTest_coefficient_physical (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧
      ∀ r : ℝ, ∀ hr : 0 < r, ∀ x : X, ∀ hx : x ∈ tsupport (A.partition p),
      ∀ v : Space, ∀ y : X,
      ‖normalizedFrameEncode A J α ht E y
        ((concentrationTest A J α ht E hE p r hr x hx v).val y)‖ ≤
      ((B/r^3)*physicalProfile J α hs ht (L*r) x y+C*r^4)*‖v‖ := by
  obtain ⟨B,hB,hcoef⟩ := planeCurrentTest_coefficient_bound A J α ht E hE p
  obtain ⟨L,hL,hprofile⟩ := compact_chart_profile_bound_points J α hs ht p.val
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
  refine ⟨48*B,B*C,L,by positivity,by positivity,hL,fun r hr x hx v y => ?_⟩
  let h := fun z => cutKernel (E p).concentrationCutoff.bump r (extChartAt Model p.val x-z)
  have hK : tsupport h ⊆ (E p).concentrationCompact :=
    (E p).concentrationCutoff.reflected_support (partition_center_ball A J α ht E hE p hx) r
  by_cases hy : y ∈ (extChartAt Model p.val).symm '' (E p).concentrationCompact
  · have hysrc : y ∈ (extChartAt Model p.val).source := by
      obtain ⟨z,hz,rfl⟩ := hy
      exact (extChartAt Model p.val).map_target ((E p).concentrationCompact_target hz)
    have hyK : extChartAt Model p.val y ∈ (E p).concentrationCompact := by
      obtain ⟨z,hz,rfl⟩ := hy
      rwa [(extChartAt Model p.val).right_inv ((E p).concentrationCompact_target hz)]
    have hh := hcoef h v (reflected_smooth _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff) _)
      (reflected_compact _ (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r) _) hK y
    rw [reflected_fderiv_norm (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff |>.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))] at hh
    have hp := hprofile x y (A.subordinate p hx) hysrc
      ((E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)) hyK r hr
    have hd := (hder r hr (extChartAt Model p.val x-extChartAt Model p.val y)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 48/r^3)) le_rfl)
    exact hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hB) (norm_nonneg v)).trans_eq (by ring))
  · change ‖normalizedFrameEncode A J α ht E y ((planeCurrentTest _ h v _ _ _).val y)‖ ≤ _
    rw [planeCurrentTest_zero_off p.val h v _ _ _ hK hy]
    change ‖normalizedFrameEncode A J α ht E y (0 : MetricForms.Form Space 2)‖ ≤ _
    rw [map_zero,norm_zero]
    exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)) (norm_nonneg _)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
attribute [local instance] unitMeasurable unitBorel unitT2 
variable {V : Type*} [NormedAddCommGroup V]

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma physicalQError_nonneg (q : X → V) {L r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ physicalQError A J α hs ht q L r x := by
  apply integral_nonneg
  intro y
  exact div_nonneg (mul_nonneg (norm_nonneg _) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)

omit [SecondCountableTopology X] in
lemma physicalQError_integrand_integrable (q : X → V)
    (hq : Integrable q (geometricVolume A J α)) {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (x : X) :
    Integrable (fun y => ‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3)
      (geometricVolume A J α) := by
  have hm : AEStronglyMeasurable (fun y => physicalProfile J α hs ht (L*r) x y) (geometricVolume A J α) :=
    ((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply (hq.norm.mul_bdd hm (c := 1) ?_).div_const
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalProfile_nonneg J α hs ht _ _ _)]
    exact physicalProfile_le_one J α hs ht (mul_pos hL hr) _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationQBound
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

include hE in
omit [SecondCountableTopology X] in
lemma concentrationTest_Q_bound (Q : L2 A J α hs ht true) (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧
      ∀ r : ℝ, ∀ hr : 0 < r, ∀ x : X, ∀ hx : x ∈ tsupport (A.partition p),
      ∀ v : Space,
      |⟪Q,smoothL2 A J α hs ht true (concentrationTest A J α ht E hE p r hr x hx v)⟫| ≤
      (B*physicalQError A J α hs ht (l2Coefficients A J α hs ht E hE Q) L r x+C*r^4)*‖v‖ := by
  let := geometricVolume_finite A J α hs ht
  let q := l2Coefficients A J α hs ht E hE Q
  have hq : Integrable q (geometricVolume A J α) := (Lp.memLp q).integrable (by norm_num)
  obtain ⟨B,C,L,hB,hC,hL,hbound⟩ := concentrationTest_coefficient_physical A J α hs ht E hE p
  refine ⟨B,C*(∫ y, ‖q y‖ ∂geometricVolume A J α),L,hB,
    mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _)),hL,fun r hr x hx v => ?_⟩
  let a := concentrationTest A J α ht E hE p r hr x hx v
  rw [l2Coefficients_pairing A J α hs ht E hE Q a]
  have hi := physicalQError_integrand_integrable A J α hs ht q hq hL hr x
  have hq' : Integrable (fun y => (C*r^4)*‖q y‖) (geometricVolume A J α) := hq.norm.const_mul _
  have hi' : Integrable (fun y => B*(‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3))
      (geometricVolume A J α) := hi.const_mul B
  have htot := (hi'.add hq').mul_const ‖v‖
  have hp (y : X) : ‖⟪q y,normalizedFrameEncode A J α ht E y (a.val y)⟫‖ ≤
      (B*(‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3)+(C*r^4)*‖q y‖)*‖v‖ :=
    (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left (hbound r hr x hx v y)
      (norm_nonneg (q y))).trans_eq (by ring))
  have hh := norm_integral_le_of_norm_le htot (ae_of_all _ hp)
  change |∫ y, ⟪q y,normalizedFrameEncode A J α ht E y (a.val y)⟫ ∂geometricVolume A J α| ≤ _
  rw [integral_mul_const] at hh
  simp only [Pi.add_apply] at hh
  rw [integral_add hi' hq',integral_const_mul,integral_const_mul] at hh
  rw [Real.norm_eq_abs] at hh
  change |∫ y, ⟪q y,normalizedFrameEncode A J α ht E y (a.val y)⟫ ∂geometricVolume A J α| ≤
    (B*(∫ y, ‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3 ∂geometricVolume A J α)+
      (C*(∫ y, ‖q y‖ ∂geometricVolume A J α))*r^4)*‖v‖
  exact hh.trans_eq (by ring)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationFirstEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 

omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma concentration_first_estimate
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (p : A.centers) {r : ℝ} (hr : 0 < r) (x : X) (hx : x ∈ tsupport (A.partition p)) (w v : Space) :
    |fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x) w| ≤
      |⟪Q,smoothL2 A J α hs ht true (concentrationTest A J α ht E hE p r hr x hx v)⟫| +
      ∫ u, (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
        (fun u => unitChartArea J α hs ht p.val u *
          |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
            (extChartAt Model p.val x-unitChartBase J α hs ht p.val u)
            (w-skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) v)|) u ∂μ := by
  let k := cutKernel (E p).concentrationCutoff.bump r
  let b := extChartAt Model p.val x
  let S := unitChartDomain J α hs ht p.val (E p).concentrationCompact
  let t := fun u => fderiv ℝ k (b-unitChartBase J α hs ht p.val u)
    (w-skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) v)
  have hk := cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff
  have htc : ContinuousOn t S :=
    ((hk.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn
      (continuousOn_const.sub (unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target))).clm_apply
      (continuousOn_const.sub (unitChartSkew_continuousOn J α hs ht p.val v (E p).concentrationCompact_target))
  have hi := planeWeighted_integrable J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ (fun u => |t u|) htc.abs
  simp only [smul_eq_mul] at hi
  have hnorm : |∫ u, S.indicator (fun u => unitChartArea J α hs ht p.val u*t u) u ∂μ| ≤
      ∫ u, S.indicator (fun u => unitChartArea J α hs ht p.val u*|t u|) u ∂μ := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hi
    apply ae_of_all
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu,indicator_of_mem hu,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg (show 0 ≤ unitChartArea J α hs ht p.val u from by exact mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    · rw [indicator_of_notMem hu,indicator_of_notMem hu,norm_zero]
  have hid := planeConvolution_first_variation J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target μ k hk
    (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r) b w v
    ((E p).concentrationCutoff.reflected_support (partition_center_ball A J α ht E hE p hx) r)
  have ht0 := hT (concentrationTest A J α ht E hE p r hr x hx v)
    (concentrationTest_closed A J α ht E hE p hr x hx v)
  change fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x) w +
    unitMeasureCurrent J (hermitianMetric J α hs ht) μ (concentrationTest A J α ht E hE p r hr x hx v) = _ at hid
  have hd : fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x) w =
      ⟪Q,smoothL2 A J α hs ht true (concentrationTest A J α ht E hE p r hr x hx v)⟫ +
      ∫ u, S.indicator (fun u => unitChartArea J α hs ht p.val u*t u) u ∂μ := by linarith
  rw [hd]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hnorm)

omit [SecondCountableTopology X] in
include hE in
lemma concentration_plane_estimate_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧ ∀ r : ℝ, 0 < r →
      ∀ u : MetricUnit (hermitianMetric J α hs ht),
      A.partition p u.val.proj *
        (|fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartFirst J α hs ht p.val u)|+
         |fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)|) ≤
      B*physicalQError A J α hs ht (l2Coefficients A J α hs ht E hE Q) L r u.val.proj+C*r^4 +
      (∫ v, variationDensity A J α hs ht E p r (v,u) ∂μ)+
      (∫ v, secondVariationDensity A J α hs ht E p r (v,u) ∂μ) := by
  obtain ⟨B,C,L,hB,hC,hL,hq⟩ := concentrationTest_Q_bound A J α hs ht E hE Q p
  refine ⟨2*B,2*C,L,by positivity,by positivity,hL,fun r hr u => ?_⟩
  have hn : 0 ≤ B*physicalQError A J α hs ht (l2Coefficients A J α hs ht E hE Q) L r u.val.proj+C*r^4 :=
    add_nonneg (mul_nonneg hB (physicalQError_nonneg A J α hs ht _ hr _)) (by positivity)
  by_cases hz : A.partition p u.val.proj = 0
  · simp only [hz,zero_mul,variationDensity,secondVariationDensity,integral_zero,add_zero]
    nlinarith
  have hx : u.val.proj ∈ tsupport (A.partition p) := subset_tsupport _ hz
  have hu := unitChartPlane J α hs ht p.val u (A.subordinate p hx)
  have hfirst := concentration_first_estimate A J α hs ht E hE μ Q hT p hr u.val.proj hx
    (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)
  have hsecond := concentration_first_estimate A J α hs ht E hE μ Q hT p hr u.val.proj hx
    (unitChartSecond J α hs ht p.val u) (-unitChartFirst J α hs ht p.val u)
  have hq1 := hq r hr u.val.proj hx (unitChartSecond J α hs ht p.val u)
  have hq2 := hq r hr u.val.proj hx (-unitChartFirst J α hs ht p.val u)
  rw [hu.2.1,mul_one] at hq1
  rw [norm_neg,hu.1,mul_one] at hq2
  have hf := mul_le_mul_of_nonneg_left (hfirst.trans (add_le_add hq1 le_rfl)) (A.partition.nonneg p u.val.proj)
  have hg := mul_le_mul_of_nonneg_left (hsecond.trans (add_le_add hq2 le_rfl)) (A.partition.nonneg p u.val.proj)
  simp only [mul_add,← integral_const_mul] at hf hg
  change _ ≤ _ + (∫ v, variationDensity A J α hs ht E p r (v,u) ∂μ) at hf
  change _ ≤ _ + (∫ v, secondVariationDensity A J α hs ht E p r (v,u) ∂μ) at hg
  have hp := mul_le_of_le_one_left hn (A.partition.le_one p u.val.proj)
  dsimp only [unitChartBase] at hf hg ⊢
  nlinarith
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate_oai.{u_1}
