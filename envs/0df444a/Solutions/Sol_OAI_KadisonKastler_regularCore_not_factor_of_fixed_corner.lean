-- Prove2me | solution 1 for OAI.KadisonKastler.regularCore_not_factor_of_fixed_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:01:11.325425+00:00
-- url     : https://prove2.me/submissions/65c6c632-e8db-4cdf-8323-cd1ed5ad193e

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K028
import Definitions.Def_Q260K071
import Theorems.Thm_OAI_KadisonKastler_regularConstant_frequencyWindow_ne_self
import Theorems.Thm_OAI_KadisonKastler_regularCore_fixed_corner_commute_translations

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorCornerCentralProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A central projection in a nonzero factor corner is trivial -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem factor_corner_central_projection (hM : ScalarCenter M)
    (p q : AlgebraProjection M) (hqp : q ≤ p)
    (hc : ∀ a : Algebra M, q.val * (p.val * a * p.val) =
      (p.val * a * p.val) * q.val) : q.val = 0 ∨ q = p := by
  classical
  by_cases hq : q.val = 0
  · exact Or.inl hq
  right
  by_contra hne
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val ≠ 0 := by
    intro h
    apply hne
    apply Subtype.ext
    exact (sub_eq_zero.mp h).symm
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c h
    obtain ⟨z, hz⟩ := hM c.val c.property
      (fun a ha => congrArg Subtype.val (h ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hf q r hq hr
  have hvq : v.val * q.val = v.val := (v.support_le_iff_mul q).mp hvs
  have hrv : r.val * v.val = v.val := (v.target_le_iff_mul r).mp hvt
  have hpr : p.val * r.val = r.val := AlgebraProjection.remainder_le q p hqp
  have hqp' : q.val * p.val = q.val := projection_mul_of_le hqp
  have hpv : p.val * v.val = v.val := by
    calc
      _ = p.val * (r.val * v.val) := by rw [hrv]
      _ = v.val := by rw [← mul_assoc, hpr, hrv]
  have hvp : v.val * p.val = v.val := by
    calc
      _ = (v.val * q.val) * p.val := by rw [hvq]
      _ = v.val := by rw [mul_assoc, hqp', hvq]
  have hqr : q.val * r.val = 0 := by
    change q.val * (p.val - q.val) = 0
    rw [mul_sub, hqp', q.property.isIdempotentElem.eq, sub_self]
  have hqv : q.val * v.val = 0 := by
    calc
      _ = q.val * (r.val * v.val) := by rw [hrv]
      _ = 0 := by rw [← mul_assoc, hqr, zero_mul]
  have hh := hc v.val
  rw [hpv, hvp, hqv, hvq] at hh
  apply hv0
  rw [← v.initial, ← hh, star_zero, zero_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCentralField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier fields of central elements in the actual regular core -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
  (P : VonNeumannAlgebra H)

omit [TopologicalSpace.SeparableSpace H] in
/-- Fixed operators have constant regular embeddings. -/
theorem regularCoreEmbedding_eq_constant_of_fixed (b : H →L[ℂ] H)
    (hfixed : ∀ s, unitaryConj (U s) b = b) :
    regularCoreEmbedding U hU b = regularConstantHom volume b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU b f,
    regularConstantHom_apply_ae volume b f] with t h₁ h₂
  rw [h₁, h₂]
  have he : unitaryConj (star (U (Multiplicative.ofAdd t))) b = b := by
    rw [regularGroup_star_eq U t]
    exact hfixed _
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    using congrArg (fun A : H →L[ℂ] H => A (f t)) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vectors supported in the bounded-frequency core corners -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_regularFrequencyPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖regularFrequencyPacket φ ξ‖ = ‖φ‖ * ‖ξ‖ := by
  rw [regularFrequencyPacket, LinearIsometryEquiv.norm_map, norm_regularTensorVector]

theorem regularFrequencyWindow_packet (a b : ℝ)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularFrequencyWindow a b (regularFrequencyPacket φ ξ) =
      regularFrequencyPacket (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc φ) ξ := by
  unfold regularFrequencyWindow regularFrequencyPacket
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    regularIndicatorProjection_tensor]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyUnitWindow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nonzero bounded frequency window in the modular core

The unit interval supplies an explicit isometric family of vectors fixed by
its frequency projection. No trace or finiteness assertion is used here.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitFrequencyScalar_fixed :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc unitFrequencyScalar =
      unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioc unitFrequencyScalar,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hp hf
  change regularIndicatorProjection _ _ unitFrequencyScalar t = unitFrequencyScalar t
  rw [hp]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · exact Set.indicator_of_mem ht _
  · rw [Set.indicator_of_notMem ht, show unitFrequencyScalar t = 0 from
      hf.trans (Set.indicator_of_notMem ht _)]

@[simp] theorem norm_unitFrequencyVector (ξ : H) : ‖unitFrequencyVector ξ‖ = ‖ξ‖ := by
  rw [unitFrequencyVector, norm_regularFrequencyPacket, norm_unitFrequencyScalar, one_mul]

theorem unitFrequencyVector_fixed (ξ : H) :
    regularFrequencyWindow 0 1 (unitFrequencyVector ξ) = unitFrequencyVector ξ := by
  rw [unitFrequencyVector, regularFrequencyWindow_packet, unitFrequencyScalar_fixed]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TrivialCoreCenter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The regular core of a trivial action has a nontrivial center -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_commute_of_translations
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s, Commute T (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) (a b : ℝ) :
    Commute T (regularFrequencyWindow a b) := by
  apply (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv.injective
  change (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (T * regularFrequencyWindow a b) =
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (regularFrequencyWindow a b * T)
  rw [map_mul, map_mul]
  have he : (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      (regularFrequencyWindow (H := H) a b) =
      regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [regularFrequencyWindow, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [he]
  exact (commute_scalarMultiplier_of_characters
    ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
    (fourier_commute_characters_of_translations T hT)
    ((Set.Ioc a b).indicator fun _ => (1 : ℂ))
    (measurable_const.indicator measurableSet_Ioc) 1
    (fun t => by by_cases ht : t ∈ Set.Ioc a b <;> simp [ht])).eq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularActionPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral action on the packets of an invariant vector -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyPacket_eq_tensor (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularFrequencyPacket φ x =
      regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ).symm φ) x := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  rw [regularFrequencyPacket, LinearIsometryEquiv.apply_symm_apply,
    fourier_regularTensorVector, LinearIsometryEquiv.apply_symm_apply]

theorem regularConstantHom_frequencyPacket (a : H →L[ℂ] H)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularConstantHom volume a (regularFrequencyPacket φ x) =
      regularFrequencyPacket φ (a x) := by
  rw [regularFrequencyPacket_eq_tensor, regularConstantHom_tensorVector,
    regularFrequencyPacket_eq_tensor]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFixedCornerObstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A pointwise fixed nonzero corner prevents factoriality of the core -/

namespace KadisonKastler

open MeasureTheory Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularConstant_frequencyWindow_ne_zero (p : H →L[ℂ] H) (hp : p ≠ 0) :
    regularConstantHom volume p * regularFrequencyWindow 0 1 ≠ 0 := by
  intro hz
  apply hp
  apply ContinuousLinearMap.ext
  intro x
  have hh := congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    T (unitFrequencyVector x)) hz
  change regularConstantHom volume p (regularFrequencyWindow 0 1 (unitFrequencyVector x)) = 0 at hh
  rw [unitFrequencyVector_fixed] at hh
  change regularConstantHom volume p (regularFrequencyPacket unitFrequencyScalar x) = 0 at hh
  rw [regularConstantHom_frequencyPacket] at hh
  have hn := congrArg norm hh
  rw [norm_zero, norm_regularFrequencyPacket, norm_unitFrequencyScalar, one_mul] at hn
  exact norm_eq_zero.mp hn

theorem regularCore_not_factor_of_fixed_corner_oai
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0)
    (hfix : ∀ t a, a ∈ M → unitaryConj (U t) (p.val.val * a * p.val.val) =
      p.val.val * a * p.val.val) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  have hp : ∀ t, unitaryConj (U t) p.val.val = p.val.val := by
    intro t
    have h := hfix t 1 M.one_mem
    simpa only [mul_one, show p.val.val * p.val.val = p.val.val from
      congrArg Subtype.val p.property.isIdempotentElem.eq] using h
  let R := regularCoreAlgebra U hU M
  let P : Algebra R := ⟨regularCoreEmbedding U hU p.val.val,
    regularCoreEmbedding_mem_core U hU M p.val.property⟩
  let W : Algebra R := ⟨regularFrequencyWindow 0 1, regularFrequencyWindow_mem_core U hU M 0 1⟩
  have hP : IsStarProjection P := by
    constructor
    · apply Subtype.ext
      exact (p.property.map M.toStarSubalgebra.subtype |>.map (regularCoreEmbedding U hU)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (p.property.map M.toStarSubalgebra.subtype |>.map (regularCoreEmbedding U hU)).isSelfAdjoint.star_eq
  have hW : IsStarProjection W := by
    constructor
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isIdempotentElem.eq
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isSelfAdjoint.star_eq
  have hPW : Commute P W := by
    apply Subtype.ext
    change Commute (regularCoreEmbedding U hU p.val.val) (regularFrequencyWindow 0 1)
    rw [regularCoreEmbedding_eq_constant_of_fixed U hU _ hp]
    exact regularFrequencyWindow_commute_of_translations _
      (regularConstant_commute_translation _) 0 1
  let p' : AlgebraProjection R := ⟨P, hP⟩
  let q : AlgebraProjection R := ⟨P * W, hP.mul hW hPW⟩
  have hqp : q ≤ p' := by
    change P * (P * W) = P * W
    rw [← mul_assoc, hP.isIdempotentElem.eq]
  intro hf
  have hc : ∀ a : Algebra R, q.val * (p'.val * a * p'.val) =
      (p'.val * a * p'.val) * q.val := by
    intro a
    have hS : Commute (P * a * P) W := by
      apply Subtype.ext
      exact (regularFrequencyWindow_commute_of_translations _
        (regularCore_fixed_corner_commute_translations U hU M hn p hfix a.val a.property) 0 1).eq
    change (P * W) * (P * a * P) = (P * a * P) * (P * W)
    calc
      _ = P * ((P * a * P) * W) := by rw [mul_assoc, hS.symm.eq]
      _ = (P * a * P) * W := by simp only [← mul_assoc, hP.isIdempotentElem.eq]
      _ = _ := by
        rw [← mul_assoc (P * a * P) P W, mul_assoc (P * a) P P,
          hP.isIdempotentElem.eq]
  rcases factor_corner_central_projection hf p' q hqp hc with hz | he
  · apply regularConstant_frequencyWindow_ne_zero p.val.val
      (fun h => hp0 (Subtype.ext h))
    have hh := congrArg Subtype.val hz
    change regularCoreEmbedding U hU p.val.val * regularFrequencyWindow 0 1 = 0 at hh
    rwa [regularCoreEmbedding_eq_constant_of_fixed U hU _ hp] at hh
  · apply regularConstant_frequencyWindow_ne_self p.val.val
      (fun h => hp0 (Subtype.ext h))
    have hh := congrArg (fun r : AlgebraProjection R => r.val.val) he
    change regularCoreEmbedding U hU p.val.val * regularFrequencyWindow 0 1 =
      regularCoreEmbedding U hU p.val.val at hh
    rwa [regularCoreEmbedding_eq_constant_of_fixed U hU _ hp] at hh

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.regularCore_not_factor_of_fixed_corner_oai.{u_1} := @OAI.KadisonKastler.regularCore_not_factor_of_fixed_corner_oai.{u_1}
