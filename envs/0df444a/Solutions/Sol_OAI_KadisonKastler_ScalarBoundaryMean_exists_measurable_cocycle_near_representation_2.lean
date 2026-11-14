-- Prove2me | solution 2 for OAI.KadisonKastler.ScalarBoundaryMean.exists_measurable_cocycle_near_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T16:12:28.848287+00:00
-- url     : https://prove2.me/submissions/f6f76de2-a718-4ecf-96ab-28315669913f

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
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K035
import Theorems.Thm_OAI_KadisonKastler_ScalarBoundaryMean_operatorMean_equivariant
import Theorems.Thm_OAI_KadisonKastler_constantAlgebraUnitaryFamily_defect_le
import Theorems.Thm_OAI_KadisonKastler_exists_bounded_cocycle_of_equivariant_mean
import Theorems.Thm_OAI_KadisonKastler_exists_measurable_operator_cocycle_with_lift
import Theorems.Thm_OAI_KadisonKastler_hasOperatorValues_of_mem
import Theorems.Thm_OAI_KadisonKastler_operatorFieldConst_representative_ae
import Theorems.Thm_OAI_KadisonKastler_unitary_family_multiplicative_defect

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equivariant averaging within a von Neumann algebra

The constant-commutant description of the field algebra is invariant under
boundary pullback. Restricting the constructed mean therefore keeps both
the cocycle and its correction in the prescribed von Neumann algebra.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H)

namespace ScalarBoundaryMean

variable {M} {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
  (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem operatorFieldFamilyInclusion_translate (M : VonNeumannAlgebra H) (g : G)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryTranslate (α.restrictedOperatorAction M) g F) =
      boundaryTranslate (α.operatorAction (H := H)) g (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := by
  ext t
  rfl

theorem restrictedOperatorMean_equivariant (M : VonNeumannAlgebra H) (g : G)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (boundaryTranslate (α.restrictedOperatorAction M) g F) =
      α.restrictedOperatorAction M g (m.restrictedOperatorMean hTom M F) := by
  apply Subtype.ext
  change m.operatorMean (H := H)
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryTranslate (α.restrictedOperatorAction M) g F)) =
    α.operatorAction (H := H) g (m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F))
  exact (congrArg (m.operatorMean (H := H))
    (operatorFieldFamilyInclusion_translate (G := G) (D := D) (H := H) (μ := μ) M g F)).trans
      (m.operatorMean_equivariant (H := H) g (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F))

include m hTom in
/-- The exact cocycle correction remains in the prescribed field algebra. -/
theorem exists_restricted_operator_cocycle (M : VonNeumannAlgebra H)
    (V : unitary (G →ᵇ operatorFieldAlgebra (μ := μ) M))
    (hV : unitaryCocycleDefect (α.restrictedOperatorAction M) V ≤ 1 / 64) :
    ∃ W : unitary (G →ᵇ operatorFieldAlgebra (μ := μ) M),
      (∀ g h, W.val g * α.restrictedOperatorAction M g (W.val h) = W.val (g * h)) ∧
      dist V W ≤ 2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V :=
  exists_bounded_cocycle_of_equivariant_mean (α.restrictedOperatorAction M)
    (m.restrictedOperatorBimoduleMean hTom M) (m.restrictedOperatorMean_equivariant hTom M) V hV

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedMeasurableCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace OAI

/-! # Measurable cocycle correction with values in a von Neumann algebra -/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace ScalarBoundaryMean

variable {α : NonsingularAction G D μ}

/-- The scalar boundary mean corrects an M-valued approximate cocycle to
an actual measurable unitary cocycle whose values remain in M. -/
theorem exists_measurable_correction_in (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (M : VonNeumannAlgebra H)
    (V : unitary (G →ᵇ operatorFieldAlgebra (μ := μ) M))
    (hV : unitaryCocycleDefect (α.restrictedOperatorAction M) V ≤ 1 / 64) :
    ∃ U : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (U g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g, ∀ᵐ x ∂μ, (U g x : H →L[ℂ] H) ∈ M) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ g, ∀ᵐ x ∂μ,
        ‖(U g x : H →L[ℂ] H) - WeakOperatorRepresentative.eval
          (WeakOperatorField.representative (V.val g : WeakOperatorField (H := H) μ)) x‖ ≤
            2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V) := by
  obtain ⟨W, hW, hd⟩ := m.exists_restricted_operator_cocycle hTom M V hV
  let inc := operatorFieldFamilyInclusion (G := G) (μ := μ) M
  let V' : unitary (G →ᵇ WeakOperatorField (H := H) μ) :=
    Unitary.map (StarMonoidHom.ofClass inc) V
  let W' : unitary (G →ᵇ WeakOperatorField (H := H) μ) :=
    Unitary.map (StarMonoidHom.ofClass inc) W
  have hW' (g h : G) :
      W'.val g * α.operatorAction (H := H) g (W'.val h) = W'.val (g * h) := by
    exact congrArg (fun q : operatorFieldAlgebra (μ := μ) M =>
      (q : WeakOperatorField (H := H) μ)) (hW g h)
  have hd' : dist V' W' ≤ 2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V := by
    rw [Subtype.dist_eq, dist_eq_norm]
    change ‖inc V.val - inc W.val‖ ≤ _
    have hd₀ : ‖V.val - W.val‖ ≤ 2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hd
    have hi : inc (V.val - W.val) = inc V.val - inc W.val := by
      ext g
      rfl
    calc
      _ = ‖inc (V.val - W.val)‖ := congrArg norm hi.symm
      _ ≤ ‖V.val - W.val‖ :=
        norm_operatorFieldFamilyInclusion_le (G := G) (μ := μ) M (V.val - W.val)
      _ ≤ _ := hd₀
  obtain ⟨U, hm, hc, hclose, hrep⟩ :=
    exists_measurable_operator_cocycle_with_lift α V' W' hW' hd'
  refine ⟨U, hm, ?_, hc, hclose⟩
  intro g
  have hv := hasOperatorValues_of_mem M
    (W.val g : WeakOperatorField (H := H) μ) (W.val g).property
  filter_upwards [hrep g, hv] with x hx hmem
  rwa [hx]

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstantFieldCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Correcting a nearby unitary family into an algebra-valued cocycle -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {N : VonNeumannAlgebra H}

namespace ScalarBoundaryMean

/-- Starting from an actual nearby unitary family, correction supplies a
measurable N-valued cocycle with the explicit total approximation bound. -/
theorem exists_measurable_cocycle_near_representation_oai
    {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (U : G →* unitary (H →L[ℂ] H)) (V : G → unitary (Algebra N))
    {e : ℝ} (he : 0 ≤ e) (hsmall : 3 * e ≤ 1 / 64)
    (hV : ∀ g, ‖(V g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ e) :
    ∃ W : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ N) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (W g x : H →L[ℂ] H) * W h (α.toPerm g⁻¹ x) = W (g * h) x) ∧
      (∀ g, ∀ᵐ x ∂μ, ‖(W g x : H →L[ℂ] H) - U g‖ ≤ 7 * e) := by
  have hdef := constantAlgebraUnitaryFamily_defect_le α V (by positivity)
    (unitary_family_multiplicative_defect U (fun g => ambientAlgebraUnitary (V g)) hV)
  obtain ⟨W, hm, hN, hc, hn⟩ := m.exists_measurable_correction_in hTom N
    (constantAlgebraUnitaryFamily (μ := μ) V) (hdef.trans hsmall)
  refine ⟨W, hm, hN, hc, ?_⟩
  intro g
  have hrep : ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval
      (WeakOperatorField.representative
        ((constantAlgebraUnitaryFamily (μ := μ) V).val g :
          WeakOperatorField (H := H) μ)) x = (V g : H →L[ℂ] H) := by
    rw [constantAlgebraUnitaryFamily_coe]
    exact operatorFieldConst_representative_ae (μ := μ) (V g : H →L[ℂ] H)
  filter_upwards [hn g, hrep] with x hx hrepr
  rw [hrepr] at hx
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (W g x : H →L[ℂ] H) (V g : H →L[ℂ] H) (U g : H →L[ℂ] H)
  linarith [hV g]

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.ScalarBoundaryMean.exists_measurable_cocycle_near_representation_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.ScalarBoundaryMean.exists_measurable_cocycle_near_representation_oai.{u_1, u_2, u_3}
