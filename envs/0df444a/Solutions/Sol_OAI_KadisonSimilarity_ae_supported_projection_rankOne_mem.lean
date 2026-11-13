-- Prove2me | solution 1 for OAI.KadisonSimilarity.ae_supported_projection_rankOne_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:41:46.29542+00:00
-- url     : https://prove2.me/submissions/32243e4b-ff49-4859-8e12-245b1fd6a8fe

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.Induction
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A033

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_BoundedMeasurableField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable operator fields on L²

Strong measurability of each constant column suffices to apply a field to
an arbitrary L² vector. An almost-everywhere uniform bound then constructs
the actual bounded L² operator, with its pointwise action and localization
commutation proved directly. No norm measurability of the operator field
is required.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem boundedFieldOperator_action
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    ∀ᵐ a ∂μ, boundedFieldOperator μ R hR C hbound f a = R a (f a) :=
  boundedFieldVector_ae μ R hR C hbound f

/-- A measurable field supported on a projection gives a genuinely
left-supported L² operator. -/
theorem boundedFieldOperator_left_support
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (P : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hsupport : ∀ᵐ a ∂μ, p a * R a = R a) :
    P * boundedFieldOperator μ R hR C hbound = boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP (boundedFieldOperator μ R hR C hbound f),
    boundedFieldOperator_action μ R hR C hbound f, hsupport] with a hpf hrf ha
  change P (boundedFieldOperator μ R hR C hbound f) a =
    boundedFieldOperator μ R hR C hbound f a
  rw [hpf, hrf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

/-- Right support is also recovered from the corresponding pointwise
identity, with no simultaneous null-set assumption. -/
theorem boundedFieldOperator_right_support
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (P : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hsupport : ∀ᵐ a ∂μ, R a * p a = R a) :
    boundedFieldOperator μ R hR C hbound * P = boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f, boundedFieldOperator_action μ R hR C hbound (P f),
    boundedFieldOperator_action μ R hR C hbound f, hsupport] with a hpf hrpf hrf ha
  change boundedFieldOperator μ R hR C hbound (P f) a =
    boundedFieldOperator μ R hR C hbound f a
  rw [hrpf, hpf, hrf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IntertwinerExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero along an isometric Hilbert-space embedding. These
identities transport the central commutant to the common scalar L² model. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

/-- Compressing an operator supported on the isometric range and extending
it back recovers the original operator. -/
theorem isometricExtension_compression
    (Q : K →L[ℂ] K)
    (hleft : isometricExtension J 1 * Q = Q)
    (hright : Q * isometricExtension J 1 = Q) :
    isometricExtension J
      ((J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap) = Q := by
  have hl (x : K) : J (J.toContinuousLinearMap.adjoint (Q x)) = Q x :=
    congrArg (fun L : K →L[ℂ] K => L x) hleft
  have hr (x : K) : Q (J (J.toContinuousLinearMap.adjoint x)) = Q x :=
    congrArg (fun L : K →L[ℂ] K => L x) hright
  apply ContinuousLinearMap.ext
  intro x
  change J (J.toContinuousLinearMap.adjoint
    (Q (J (J.toContinuousLinearMap.adjoint x)))) = Q x
  rw [hr, hl]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionRankOne
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported rank-one fields supply countably many tests for the full
operator algebra on each projection range. Their bounds and measurability
follow from the projection columns themselves. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A rank-one operator with both vectors in a projection range is supported
on that range on both sides. -/
theorem projection_rankOne_support (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) :
    p * InnerProductSpace.rankOne ℂ (p v) (p w) =
        InnerProductSpace.rankOne ℂ (p v) (p w) ∧
      InnerProductSpace.rankOne ℂ (p v) (p w) * p =
        InnerProductSpace.rankOne ℂ (p v) (p w) := by
  have hpp (x : H) : p (p x) = p x :=
    congrArg (fun L : H →L[ℂ] H => L x) hp.isIdempotentElem.eq
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change p (inner ℂ (p w) x • p v) = inner ℂ (p w) x • p v
    rw [map_smul, hpp]
  · apply ContinuousLinearMap.ext
    intro x
    change inner ℂ (p w) (p x) • p v = inner ℂ (p w) x • p v
    have ha : p.adjoint (p w) = p w := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq, hpp]
    rw [← ContinuousLinearMap.adjoint_inner_left, ha]

/-- Compression gives the ordinary rank-one operator on the range. -/
theorem projectionFiberCompression_rankOne (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) :
    projectionFiberCompression p hp (InnerProductSpace.rankOne ℂ (p v) (p w)) =
      InnerProductSpace.rankOne ℂ (projectionFiberRetraction p hp v)
        (projectionFiberRetraction p hp w) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p (inner ℂ (p w) (x : H) • p v) = inner ℂ (p w) (x : H) • p v
  rw [map_smul]
  exact congrArg (_ • ·) (congrArg (fun L : H →L[ℂ] H => L v) hp.isIdempotentElem.eq)

theorem norm_projection_apply_le (p : H →L[ℂ] H) (hp : IsStarProjection p) (v : H) :
    ‖p v‖ ≤ ‖v‖ := by
  calc
    ‖p v‖ ≤ ‖p‖ * ‖v‖ := p.le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (norm_projection_le_one p hp.isSelfAdjoint.star_eq hp.isIdempotentElem.eq) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem norm_projection_rankOne_le (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) : ‖InnerProductSpace.rankOne ℂ (p v) (p w)‖ ≤ ‖v‖ * ‖w‖ := by
  rw [InnerProductSpace.norm_rankOne]
  exact mul_le_mul (norm_projection_apply_le p hp v) (norm_projection_apply_le p hp w)
    (norm_nonneg _) (norm_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

omit [CompleteSpace H] in
/-- Strongly measurable projection columns give strongly measurable
columns for every supported rank-one field. -/
theorem aestronglyMeasurable_projection_rankOne
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ v : H, AEStronglyMeasurable (fun a => p a v) μ) (v w x : H) :
    AEStronglyMeasurable
      (fun a => InnerProductSpace.rankOne ℂ (p a v) (p a w) x) μ := by
  exact ((hmeas w).inner aestronglyMeasurable_const).smul (hmeas v)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SupportedFieldRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported measurable fields are recovered exactly by compression to the
original Hilbert space. In particular, the supported rank-one tests used for
factor fibers come from actual original operators. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω H F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure Ω) (J : H →ₗᵢ[ℂ] Lp F 2 μ)

/-- An operator field supported on the original range is exactly the
zero extension of its compression. -/
theorem isometricExtension_boundedField_compression
    (p R : Ω → F →L[ℂ] F)
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (hmeas : ∀ v : F, AEStronglyMeasurable (fun x => R x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖R x‖ ≤ C)
    (hleft : ∀ᵐ x ∂μ, p x * R x = R x)
    (hright : ∀ᵐ x ∂μ, R x * p x = R x) :
    isometricExtension J
      ((J.toContinuousLinearMap.adjoint.comp (boundedFieldOperator μ R hmeas C hbound)).comp
        J.toContinuousLinearMap) = boundedFieldOperator μ R hmeas C hbound :=
  isometricExtension_compression J _
    (boundedFieldOperator_left_support μ R hmeas C hbound _ p hP hleft)
    (boundedFieldOperator_right_support μ R hmeas C hbound _ p hP hright)

variable [IsFiniteMeasure μ]

/-- The projection columns of the original range are strongly measurable. -/
theorem aestronglyMeasurable_isometric_projection_column
    (p : Ω → F →L[ℂ] F)
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (v : F) : AEStronglyMeasurable (fun x => p x v) μ :=
  (Lp.aestronglyMeasurable (isometricExtension J 1 (Lp.const 2 μ v))).congr
    (pointwise_action_column μ _ p hP v)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SupportedRankOneMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Abstract isometric compression supplies supported rank-one members of
the actual fiber bicommutants. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {Ω F H B : Type u} [MeasurableSpace Ω] [CStarAlgebra B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem ae_supported_projection_rankOne_mem_oai (μ : Measure Ω) [IsFiniteMeasure μ]
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (hcompression : ∀ (R : Ω → F →L[ℂ] F)
      (hm : ∀ z, AEStronglyMeasurable (fun x => R x z) μ)
      (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ C),
      ((J.toContinuousLinearMap.adjoint.comp (boundedFieldOperator μ R hm C hb)).comp
        J.toContinuousLinearMap) ∈ representationVonNeumannAlgebra σ)
    (v w : F) :
    ∀ᵐ x ∂μ, InnerProductSpace.rankOne ℂ
      (projectionFiberRetraction
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) v)
      (projectionFiberRetraction
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) w) ∈
      representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  let p := fun x => nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x)
  have hp (x) : IsStarProjection (p x) :=
    nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)
  have hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J 1 f x = p x (f x) := by
    intro f
    have h := zeroExtendOperatorField_action μ s hs hnull
      (isometricExtension J (σ 1)) (fun x => ρ x (Unitization.inr 1)) (hρ 1) f
    simpa only [map_one, zeroExtendNonunitalRepresentation_apply, nonunitalUnitProjection,
      p] using h
  let R := fun x => InnerProductSpace.rankOne ℂ (p x v) (p x w)
  have hm : ∀ z, AEStronglyMeasurable (fun x => R x z) μ :=
    aestronglyMeasurable_projection_rankOne μ p
      (aestronglyMeasurable_isometric_projection_column μ J p hP) v w
  have hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ ‖v‖ * ‖w‖ :=
    Eventually.of_forall fun x => norm_projection_rankOne_le (p x) (hp x) v w
  let Q := boundedFieldOperator μ R hm (‖v‖ * ‖w‖) hb
  let T := (J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap
  have hT : T ∈ representationVonNeumannAlgebra σ := hcompression R hm _ hb
  have he : isometricExtension J T = Q :=
    isometricExtension_boundedField_compression μ J p R hP hm _ hb
      (Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).1)
      (Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).2)
  have haction : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J T f x = R x (f x) := by
    intro f
    rw [he]
    exact boundedFieldOperator_action μ R hm _ hb f
  have hmem := ae_global_projection_mem_of_isometric_closure μ s hs hnull J σ ρ hρ
    T hT R haction
  filter_upwards [hmem] with x hx
  change projectionFiberCompression (p x) (hp x)
    (InnerProductSpace.rankOne ℂ (p x v) (p x w)) ∈ _ at hx
  rw [projectionFiberCompression_rankOne] at hx
  exact hx

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.ae_supported_projection_rankOne_mem_oai.{u} := @OAI.KadisonSimilarity.ae_supported_projection_rankOne_mem_oai.{u}
