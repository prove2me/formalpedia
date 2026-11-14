-- Prove2me | solution 1 for OAI.KadisonKastler.productBoundaryClass_close
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:12:37.551503+00:00
-- url     : https://prove2.me/submissions/1120398c-80f9-4d1a-962e-3faaaa441df9

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
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
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
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
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K069

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakOperatorFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.operatorFieldFamilyCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.constantFieldRepresentation_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.normUltraproductInducedMap_apply_map _root_.OAI.KadisonKastler.operatorFieldFamilyInclusion_apply _root_.OAI.KadisonKastler.productBoundaryClass_apply _root_.OAI.KadisonKastler.productBoundaryRepresentative_eval _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Essentially bounded weak operator fields

The representatives are bounded operator-valued functions with measurable
evaluations of the function and its adjoint. Their closed C-star algebra
is quotiented by the closed star ideal of almost-everywhere zero fields.
The resulting norm is bounded by every essential operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [MeasurableSpace D] (μ : Measure D)

attribute [local instance] OAI.KadisonKastler.weakOperatorRepresentativeOrder
attribute [local instance] OAI.KadisonKastler.weakOperatorRepresentativeStarOrder
/-- An essential operator-norm bound bounds the actual quotient norm.
The exceptional-set replacement is legitimate even when that set itself
has not been supplied as a measurable set. -/
theorem operatorFieldQuotient_norm_le_of_ae
    (F : WeakOperatorRepresentative (H := H) μ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᵐ x ∂μ, ‖WeakOperatorRepresentative.eval F x‖ ≤ C) :
    ‖operatorFieldQuotient μ F‖ ≤ C := by
  let f : D → H →L[ℂ] H := fun x =>
    if ‖WeakOperatorRepresentative.eval F x‖ ≤ C then WeakOperatorRepresentative.eval F x else 0
  have hnorm (x : D) : ‖f x‖ ≤ C := by
    dsimp [f]
    split_ifs with hx
    · exact hx
    · simpa only [norm_zero] using hC
  have heq : WeakOperatorRepresentative.eval F =ᵐ[μ] f :=
    hF.mono fun x hx => by simp [f, hx]
  have hm (ξ : H) : AEStronglyMeasurable (fun x => f x ξ) μ :=
    (WeakOperatorRepresentative.eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T => T ξ) hx)
  have hs (ξ : H) : AEStronglyMeasurable (fun x => star (f x) ξ) μ :=
    (WeakOperatorRepresentative.star_eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T : H →L[ℂ] H => star T ξ) hx)
  let G := WeakOperatorRepresentative.mk f C hnorm hm hs
  have hFG : operatorFieldQuotient μ F = operatorFieldQuotient μ G :=
    (operatorFieldQuotient_eq_iff μ F G).mpr heq
  rw [hFG]
  exact (operatorFieldQuotient_norm_le μ G).trans
    (WeakOperatorRepresentative.norm_mk_le f hC hnorm hm hs)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugateOperatorMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two-sided product boundary cocycle

Standard tracial conjugation turns the second copy into a commuting right
action. The resulting product cocycle is close to the product representation
with the explicit error `2 * δ + 2 * κ`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Moving the two conjugations costs at most twice their distance. -/
theorem norm_conjugationOperator_change_le (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (a : H →L[ℂ] H) :
    ‖conjugationOperator J₁ a - conjugationOperator J₂ a‖ ≤
      2 * ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ * ‖a‖ := by
  let d : H →L⋆[ℂ] H := (J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  change ‖J₁ (a (J₁ ξ)) - J₂ (a (J₂ ξ))‖ ≤ _
  calc
    _ ≤ ‖J₁ (a (J₁ ξ)) - J₂ (a (J₁ ξ))‖ +
        ‖J₂ (a (J₁ ξ)) - J₂ (a (J₂ ξ))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖d (a (J₁ ξ))‖ + ‖a (J₁ ξ - J₂ ξ)‖ := by
      rw [← map_sub J₂, J₂.norm_map, map_sub]
      rfl
    _ ≤ ‖d‖ * (‖a‖ * ‖ξ‖) + ‖a‖ * (‖d‖ * ‖ξ‖) := by
      apply add_le_add
      · exact (d.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [J₁.norm_map] using a.le_opNorm (J₁ ξ)) (norm_nonneg d))
      · exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (d.le_opNorm ξ) (norm_nonneg a))
    _ = _ := by dsimp only [d] <;> ring

variable {G D : Type*} [Group G]

/-- Perturbing two unitary factors and the conjugation has an additive bound. -/
theorem norm_product_conjugation_sub_le
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (hJ₂ : Function.Involutive J₂)
    (a b c d : unitary (H →L[ℂ] H))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hab : ‖(a : H →L[ℂ] H) - b‖ ≤ δ)
    (hcd : ‖(c : H →L[ℂ] H) - d‖ ≤ δ)
    (hJ : ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ ≤ κ) :
    ‖(a : H →L[ℂ] H) * conjugationOperator J₂ c -
      (b : H →L[ℂ] H) * conjugationOperator J₁ d‖ ≤ 2 * δ + 2 * κ := by
  have hC : ‖conjugationOperator J₂ c‖ ≤ 1 := by
    rw [norm_conjugationOperator J₂ hJ₂]
    exact norm_unitary_le_one c
  have hCC : ‖conjugationOperator J₂ c - conjugationOperator J₁ d‖ ≤ δ + 2 * κ := by
    calc
      _ ≤ ‖conjugationOperator J₂ c - conjugationOperator J₂ d‖ +
          ‖conjugationOperator J₂ d - conjugationOperator J₁ d‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + 2 * κ := by
        apply add_le_add
        · exact (norm_conjugationOperator_sub J₂ hJ₂ c d).le.trans hcd
        · calc
            _ = ‖conjugationOperator J₁ d - conjugationOperator J₂ d‖ := norm_sub_rev _ _
            _ ≤ 2 * ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ * ‖(d : H →L[ℂ] H)‖ :=
              norm_conjugationOperator_change_le _ _ _
            _ ≤ 2 * κ * 1 := mul_le_mul
              (mul_le_mul_of_nonneg_left hJ (by positivity)) (norm_unitary_le_one d)
              (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
  calc
    _ = ‖((a : H →L[ℂ] H) - b) * conjugationOperator J₂ c +
        (b : H →L[ℂ] H) * (conjugationOperator J₂ c - conjugationOperator J₁ d)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖((a : H →L[ℂ] H) - b) * conjugationOperator J₂ c‖ +
        ‖(b : H →L[ℂ] H) * (conjugationOperator J₂ c - conjugationOperator J₁ d)‖ := norm_add_le _ _
    _ ≤ (δ * 1) + (1 * (δ + 2 * κ)) := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_mul hab hC (norm_nonneg _) hδ)
      · exact (norm_mul_le _ _).trans
          (mul_le_mul (norm_unitary_le_one b) hCC (norm_nonneg _) (by norm_num))
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableProductCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The product cocycle as a measurable operator class

The pointwise two-sided field is measurable and uniformly unitary. Its
class satisfies the separate-action cocycle law even when the original
cocycle and algebra-membership statements hold only almost everywhere.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace D]
  [TopologicalSpace.SeparableSpace H] in
/-- The two individual approximation inequalities suffice for the product bound. -/
theorem productBoundaryValue_close_at {M N : VonNeumannAlgebra H}
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) - (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ)
    (g : G × G) (x : D × D)
    (hl : ‖(W g.1 x.1 : H →L[ℂ] H) - (U g.1 : Algebra M).val‖ ≤ δ)
    (hr : ‖(W g.2 x.2 : H →L[ℂ] H) - (U g.2 : Algebra M).val‖ ≤ δ) :
    ‖(productBoundaryValue pN W g x : H →L[ℂ] H) -
      (productBoundaryRepresentation pM U g : H →L[ℂ] H)‖ ≤ 2 * δ + 2 * κ := by
  exact norm_product_conjugation_sub_le pM.conjugation pN.conjugation
    pN.conjugation_involutive (W g.1 x.1)
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.1))
    (W g.2 x.2) (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.2))
    hδ hκ hl hr hJ

/-- Essential original closeness bounds the uniform norm of the product classes. -/
theorem productBoundaryClass_close_oai {M N : VonNeumannAlgebra H}
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : H →L[ℂ] H) - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) - (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ) :
    ‖(productBoundaryClass pN W hW).val - (productBoundaryConstantFamily (μ := μ) pM U).val‖ ≤
      2 * δ + 2 * κ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro g
  change ‖operatorFieldQuotient (H := H) (μ.prod μ)
      (productBoundaryRepresentative pN W hW g : WeakOperatorRepresentative (H := H) (μ.prod μ)) -
        operatorFieldConst (H := H) (μ.prod μ) (productBoundaryRepresentation pM U g)‖ ≤ _
  change ‖operatorFieldQuotient (H := H) (μ.prod μ) _ -
    operatorFieldQuotient (H := H) (μ.prod μ)
      (operatorRepresentativeConst (μ.prod μ) (productBoundaryRepresentation pM U g))‖ ≤ _
  rw [← map_sub]
  apply operatorFieldQuotient_norm_le_of_ae (μ.prod μ) _ (by positivity)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hclose g.1),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hclose g.2)] with x hl hr
  exact productBoundaryValue_close_at pM pN U W hδ hκ hJ g x hl hr

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.productBoundaryClass_close_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.productBoundaryClass_close_oai.{u_1, u_2, u_3}
