-- Prove2me | solution 1 for OAI.KadisonKastler.exists_product_boundary_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:12:35.916809+00:00
-- url     : https://prove2.me/submissions/82b574e2-41b5-40c7-b32d-fceb5869823d

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
import Definitions.Def_Q260K032
import Definitions.Def_Q260K069
import Theorems.Thm_OAI_KadisonKastler_ScalarBoundaryMean_operatorMean_equivariant
import Theorems.Thm_OAI_KadisonKastler_WeakOperatorField_exists_unitary_lift
import Theorems.Thm_OAI_KadisonKastler_exists_unitary_boundary_intertwiner
import Theorems.Thm_OAI_KadisonKastler_productBoundaryClass_close
import Theorems.Thm_OAI_KadisonKastler_productBoundaryClass_cocycle

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.operatorFieldFamilyCStar _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary representatives of measurable operator classes

The AE-zero ideal has a useful lifting property: every unitary quotient
class has an everywhere unitary, weakly measurable representative. Only a
null set is changed, so no selection theorem is needed.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

theorem unitaryEval_measurable (V : unitary (WeakOperatorRepresentative (H := H) μ)) (ξ : H) :
    AEStronglyMeasurable (fun x => (unitaryEval V x : H →L[ℂ] H) ξ) μ :=
  eval_aestronglyMeasurable _ ξ

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableBoundaryIntertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable representatives of the averaged boundary intertwiner

The operator-field mean and polar normalization construct the intertwiner
in the quotient algebra. The null ideal then gives the exact measurable
operator identity needed by the finite-factor argument.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace ScalarBoundaryMean

/-- The averaged polar intertwiner has measurable everywhere-unitary
values, the same norm bound, and the exact covariance almost everywhere. -/
theorem exists_measurable_boundary_intertwiner
    {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (S : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hS : ∀ g h, S.val g * α.operatorAction (H := H) g (S.val h) = S.val (g * h))
    (R : G → unitary (WeakOperatorRepresentative (H := H) μ))
    (hR : ∀ g, operatorFieldQuotient (H := H) μ (R g) = S.val g)
    (U : G →* unitary (H →L[ℂ] H))
    {δ : ℝ} (hδ : δ < 1)
    (hclose : ∀ g, ‖S.val g - operatorFieldConst μ (U g)‖ ≤ δ) :
    ∃ L : D → unitary (H →L[ℂ] H),
      (∀ ξ, AEStronglyMeasurable (fun x => (L x : H →L[ℂ] H) ξ) μ) ∧
      (∀ᵐ x ∂μ, ‖(L x : H →L[ℂ] H) - 1‖ ≤ 2 * δ) ∧
      (∀ g, ∀ᵐ x ∂μ,
        (L x : H →L[ℂ] H) * U g =
          (WeakOperatorRepresentative.unitaryEval (R g) x : H →L[ℂ] H) *
            L (α.toPerm g⁻¹ x)) := by
  let Uc : G →* unitary (WeakOperatorField (H := H) μ) :=
    constantFieldRepresentation (μ := μ) U
  have hUc (g t : G) : α.operatorAction (H := H) g (Uc t : WeakOperatorField (H := H) μ) =
      (Uc t : WeakOperatorField (H := H) μ) := by
    dsimp only [Uc]
    rw [constantFieldRepresentation_coe]
    exact α.operatorAction_constant g (U t : H →L[ℂ] H)
  have hclose' (g : G) : ‖S.val g - (Uc g : WeakOperatorField (H := H) μ)‖ ≤ δ :=
    by
      dsimp only [Uc]
      rw [constantFieldRepresentation_coe]
      exact hclose g
  obtain ⟨L₀, hL₀, hn⟩ := exists_unitary_boundary_intertwiner
    (α.operatorAction (H := H)) (m.operatorBimoduleMean hTom)
    m.operatorMean_equivariant S hS Uc hUc hδ hclose'
  obtain ⟨V, hV⟩ := WeakOperatorField.exists_unitary_lift L₀
  refine ⟨WeakOperatorRepresentative.unitaryEval V,
    WeakOperatorRepresentative.unitaryEval_measurable V, ?_, ?_⟩
  · have hnorm : ‖operatorFieldQuotient (H := H) μ
        ((V : WeakOperatorRepresentative (H := H) μ) - 1)‖ ≤ 2 * δ := by
      rw [_root_.map_sub, _root_.map_one, hV]
      exact hn
    filter_upwards [operatorField_ae_norm_le
      ((V : WeakOperatorRepresentative (H := H) μ) - 1)] with x hx
    exact hx.trans hnorm
  · intro g
    have heq : operatorFieldQuotient (H := H) μ
        ((V : WeakOperatorRepresentative (H := H) μ) *
          operatorRepresentativeConst μ (U g : H →L[ℂ] H)) =
        operatorFieldQuotient (H := H) μ
          ((R g : WeakOperatorRepresentative (H := H) μ) *
            WeakOperatorRepresentative.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹) V) := by
      rw [map_mul, map_mul, hV, hR g, ← WeakOperatorField.pullback_quotient, hV]
      exact hL₀ g
    exact (operatorFieldQuotient_eq_iff μ _ _).mp heq

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryIntertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The measurable product intertwiner in common tracial position -/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

/-- The two commuting boundary actions have a measurable unitary
intertwiner close to the identity, using the actual product mean. -/
theorem exists_product_boundary_intertwiner_oai
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (α : NonsingularAction G D μ) (m₂ : ScalarBoundaryMean α.prod)
    (hTom : PublishedFieldTomiyama (G := G × G) (H := H) (μ := μ.prod μ))
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (hWN : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ N)
    (hc : ∀ g h, ∀ᵐ x ∂μ,
      (W g x : H →L[ℂ] H) * W h (α.toPerm g⁻¹ x) = W (g * h) x)
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hsmall : 2 * δ + 2 * κ < 1)
    (hclose : ∀ g, ∀ᵐ x ∂μ,
      ‖(W g x : H →L[ℂ] H) - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) -
      (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ) :
    ∃ L : D × D → unitary (H →L[ℂ] H),
      (∀ ξ, AEStronglyMeasurable (fun x => (L x : H →L[ℂ] H) ξ) (μ.prod μ)) ∧
      (∀ᵐ x ∂μ.prod μ, ‖(L x : H →L[ℂ] H) - 1‖ ≤ 4 * δ + 4 * κ) ∧
      (∀ g, ∀ᵐ x ∂μ.prod μ,
        (L x : H →L[ℂ] H) * productBoundaryRepresentation pM U g =
          (productBoundaryValue pN W g x : H →L[ℂ] H) *
            L (α.prod.toPerm g⁻¹ x)) := by
  let S := productBoundaryClass pN W hW
  have hSc := productBoundaryClass_cocycle pN α W hW hWN hc
  have hSn := productBoundaryClass_close pM pN U W hW hδ hκ hclose hJ
  obtain ⟨L, hm, hn, hi⟩ := m₂.exists_measurable_boundary_intertwiner hTom S hSc
    (productBoundaryRepresentative pN W hW) (fun _ => rfl)
    (productBoundaryRepresentation pM U) hsmall (fun g =>
      ((S.val - (productBoundaryConstantFamily (μ := μ) pM U).val).norm_coe_le_norm g).trans hSn)
  refine ⟨L, hm, ?_, hi⟩
  filter_upwards [hn] with x hx
  linarith

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_product_boundary_intertwiner_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_product_boundary_intertwiner_oai.{u_1, u_2, u_3}
