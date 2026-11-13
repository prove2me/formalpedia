-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_normal_triple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:51:06.546578+00:00
-- url     : https://prove2.me/submissions/828c5e80-57e9-4c36-bb02-a8f0ab16efbe

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_longitudinal_profile
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_transverse_profiles

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem primitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  (rawPrimitive_hasDerivAt hf x).sub_const _

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma angleOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (angleOn F S hS hF p (t : Period)) t := by
  rw [angleOn, bundleOn_apply _ _ _ _ _ hp]
  exact angle_hasDerivAt hS hF hp t

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma primitiveOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    primitiveOn F S hS hF hm p (t : Period) =
      PeriodicPrimitive.primitive (fun s => F p (s : Period)) t :=
  bundleOn_apply _ _ _ _ _ hp t

lemma primitiveOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveOn F S hS hF hm p (s : Period)) (F p (t : Period)) t := by
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_hasDerivAt ((F p).continuous.comp (AddCircle.continuous_mk' 1)) t

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

lemma angle_hasDerivAt (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.val p (s : Period)) (F.angle.val p (t : Period)) t := by
  rw [angle, ofLocal_apply _ _ hp]
  exact angleOn_hasDerivAt F.val O O.isOpen F.smooth hp t

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitive_angle (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0) :
    (F.primitive hm).angle = F := by
  ext p hp t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := (F.primitive hm).angle_hasDerivAt hp x
  have he : (fun s : ℝ => (F.primitive hm).val p (s : Period)) =
      fun s : ℝ => primitiveOn F.val O O.isOpen F.smooth hm p (s : Period) := by
    funext s
    exact ofLocal_apply _ _ hp _
  rw [he] at hd
  exact hd.unique (primitiveOn_hasDerivAt _ _ _ _ _ hp x)

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicExpansionInit
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial coefficient and transverse cancellation on the admissible domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

omit [FiniteDimensional ℝ E] in
lemma initial_angle : g.initial.angle = g.V - g.V.vectorMean :=
  Family.primitive_angle _ _

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalAnsatzProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading jets of the supported local ansatz are the geometric profiles
of the initial periodic primitive. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open PeriodicExpansion (directionalMap)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma global_angle_eq_local (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : W.val = U.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.val p t = U.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.angle_apply,Family.angle_apply U hp,hW]

namespace Geometry

variable [FiniteDimensional ℝ A] [CompleteSpace E]
  {dy : A} (g : Geometry (E := E) O dy)

/-- The leading angular correction is the mean-zero velocity primitive. -/
lemma initial_global_angle (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.val p t = g.V.val p t-average (g.V.val p) := by
  rw [global_angle_eq_local W g.initial hW hp,g.initial_angle]
  simp only [Family.sub_apply,Family.vectorMean_apply]

/-- Adding the leading angular correction to the old longitudinal derivative
gives precisely the prescribed velocity profile `X`. -/
lemma initial_global_longitudinal {F : A → E} (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) (dx : A)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    {p : A} (hp : p ∈ O) (t : Period) :
    directionalMap F dx p+W.angle.val p t = g.longitudinal.val p t := by
  rw [g.initial_global_angle W hW hp]
  change fderiv ℝ F p dx+(g.V.val p t-average (g.V.val p)) = _
  rw [hX p hp]
  simp only [longitudinal,Family.add_apply,Family.constant_apply _ _ hp]
  abel

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma euclideanVelocity_mean {J : LowJet} (hJ : J ∈ O) :
    average (l.euclideanVelocity J) = ι (normal J) := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [l.euclideanVelocity_apply hJ]
  have hi : IntervalIntegrable (fun t => l.velocity (J, t)) MeasureTheory.volume 0 1 :=
    (smooth_slice O.isOpen l.smoothVelocity hJ).continuous.intervalIntegrable 0 1
  exact (JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.intervalIntegral_comp_comm hi).trans
    (congrArg ι (l.mean J hJ))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion
local notation "ι" => JetVelocityCoordinates.toEuclidean

lemma first_slot {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    slot (![1, 2] i) (lowJet G p) = fderiv ℝ G p (coordinateVector i) := by
  funext a
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_apply (hG.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => G q a) p (coordinateVector i) := by fin_cases i <;> rfl
    _ = _ := he

lemma euclidean_first_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector i) =
      ι (slot (![1, 2] i) (lowJet G p)) := by
  have hd := (JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp p
    (hG.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = ι (fderiv ℝ G p (coordinateVector i)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector i)) hd
    _ = _ := congrArg ι (first_slot hG i p).symm

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

lemma geometry_mean {p : JetPolynomial.Base} (hp : p ∈ S) :
    average ((l.geometry G hG hGO).V.val p) = ι (normal (lowJet G p)) := by
  rw [l.geometry_velocity hG hGO hp]
  exact l.euclideanVelocity_mean (hGO hp)

lemma geometry_dx {p : JetPolynomial.Base} (hp : p ∈ S) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 0) =
      (l.geometry G hG hGO).X₀ p + average ((l.geometry G hG hGO).V.val p) := by
  rw [euclidean_first_derivative hG, l.geometry_mean hG hGO hp]
  change ι (slot 1 (lowJet G p)) = ι (tangent (lowJet G p)) + ι (normal (lowJet G p))
  rw [← map_add]
  congr 1
  dsimp [tangent]
  abel

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformPrimitiveNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite coefficients used for the metric expansion preserve
transverse normal acceleration uniformly over a compact low-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma geometry_longitudinal_coordinates {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    spaceCoordinates ((l.geometry G hG hGO).longitudinal.val p (t : Period)) =
      VelocityFrame.leadingTangent (slot 1 (lowJet G p)) (slot 2 (lowJet G p))
        (slot 6 (lowJet G p)) (l.velocity (lowJet G p,t)) := by
  rw [LocalPeriodicExpansion.Geometry.longitudinal,Family.add_apply,
    Family.constant_apply _ _ hp,map_add,l.geometry_velocity hG hGO hp,
    l.euclideanVelocity_apply (hGO hp)]
  change spaceCoordinates (JetVelocityCoordinates.toEuclidean (tangent (lowJet G p)))+
    l.velocity (lowJet G p,t) = _
  simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply,
    tangent,normal,VelocityFrame.leadingTangent]

theorem uniform_primitive_normal_triple_oai {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        ‖primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p-
          ![VelocityFrame.leadingTangent (slot 1 (lowJet G p)) (slot 2 (lowJet G p))
            (slot 6 (lowJet G p)) (l.velocity (lowJet G p,ℓ p/z)),
            slot 2 (lowJet G p),slot 6 (lowJet G p)]‖ ≤ D*z/s^loss := by
  obtain ⟨lx,hxb⟩ := l.uniform_longitudinal_profile (S := S) hQ hQO n ℓ hx
  obtain ⟨ly,hyb⟩ := l.uniform_transverse_profiles (S := S) hQ hQO n ℓ hy
  refine ⟨max lx ly,?_⟩
  intro B hB
  obtain ⟨Dx,hDx,hxb⟩ := hxb B hB
  obtain ⟨Dy,hDy,hyb⟩ := hyb B hB
  let D := ‖spaceCoordinates.toContinuousLinearMap‖*(Dx+Dy)
  refine ⟨D,mul_nonneg (norm_nonneg _) (add_nonneg hDx hDy),?_⟩
  intro G hG hGQ s z hz hzs hs1 hb U hU hrep hinit p hp
  have hs : 0 < s := hz.trans_le hzs
  have hGO : MapsTo (lowJet G) S O := fun _ hq => hQO (hGQ hq)
  let F := fun q => JetVelocityCoordinates.toEuclidean (G q)
  let f := finiteAnsatz F U ℓ (n+1) z
  let g := l.geometry G hG hGO
  have hbound (C : ℝ) (hC : 0 ≤ C) (hC' : C ≤ Dx+Dy)
      (d : ℕ) (hd : d ≤ max lx ly) : C*z/s^d ≤ (Dx+Dy)*z/s^(max lx ly) := by
    calc
      _ ≤ C*z/s^(max lx ly) := div_le_div_of_nonneg_left (mul_nonneg hC hz.le)
        (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1 hd)
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hz.le)
        (pow_nonneg hs.le _)
  have hxerr := (hxb G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Dx hDx (by linarith) lx (le_max_left _ _))
  obtain ⟨hyerr,hyyerr⟩ := hyb G hG hGQ s z hz hzs hs1 hb U hU hrep p hp
  have hdy := hbound Dy hDy (by linarith) ly (le_max_right _ _)
  replace hyerr := hyerr.trans hdy
  replace hyyerr := hyyerr.trans hdy
  let W := globalCoefficients U hU
  have hW : (W 0).val = g.initial.val := by
    change (U 0).val = g.initial.val
    rw [hinit]
  have hx0 := g.initial_global_longitudinal (W 0) hW (coordinateVector 0)
    (fun q hq => l.geometry_dx hG hGO hq) hp ((ℓ p/z : ℝ) : Period)
  rw [global_angle_eq_local (W 0) (U 0) rfl hp] at hx0
  change PeriodicExpansion.directionalMap F (coordinateVector 0) p+
    (U 0).angle.fastValue ℓ z p = g.longitudinal.val p ((ℓ p/z : ℝ) : Period) at hx0
  rw [hx0] at hxerr
  have hy0 : PeriodicExpansion.directionalMap F (coordinateVector 1) =
      fun q => JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G q)) := by
    funext q
    exact euclidean_first_derivative hG 1 q
  rw [hy0] at hyerr hyyerr
  change ‖PeriodicExpansion.directionalMap f (coordinateVector 1) p-
    JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G p))‖ ≤ _ at hyerr
  change ‖PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 1))
    (coordinateVector 1) p-fderiv ℝ (fun q =>
      JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G q))) p (coordinateVector 1)‖ ≤ _ at hyyerr
  rw [euclidean_y_derivative hG] at hyyerr
  have hcoord {u v : Euclidean} (he : ‖u-v‖ ≤ (Dx+Dy)*z/s^(max lx ly)) :
      ‖spaceCoordinates u-spaceCoordinates v‖ ≤ D*z/s^(max lx ly) := by
    calc
      _ = ‖spaceCoordinates (u-v)‖ := by rw [map_sub]
      _ ≤ ‖spaceCoordinates.toContinuousLinearMap‖*‖u-v‖ :=
        spaceCoordinates.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖spaceCoordinates.toContinuousLinearMap‖*((Dx+Dy)*z/s^(max lx ly)) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = _ := by dsimp [D] <;> ring
  have hxc := hcoord hxerr
  rw [l.geometry_longitudinal_coordinates hG hGO hp] at hxc
  have hyc := hcoord hyerr
  have hyyc := hcoord hyyerr
  simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply] at hyc hyyc
  refine (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
    (add_nonneg hDx hDy)) hz.le) (pow_nonneg hs.le _))).mpr ?_
  intro k
  fin_cases k
  · exact hxc
  · exact hyc
  · exact hyyc

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_normal_triple_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_normal_triple_oai
