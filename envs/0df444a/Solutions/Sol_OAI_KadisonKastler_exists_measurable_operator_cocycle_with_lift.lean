-- Prove2me | solution 1 for OAI.KadisonKastler.exists_measurable_operator_cocycle_with_lift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:29:33.57712+00:00
-- url     : https://prove2.me/submissions/653820b5-b066-4409-9776-5a307633da94

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
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
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
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
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
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
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
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
import Definitions.Def_Q260K022

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

namespace WeakOperatorField

/-- A unitary operator class lifts to a unitary measurable representative. -/
theorem exists_unitary_lift (U : unitary (WeakOperatorField (H := H) μ)) :
    ∃ V : unitary (WeakOperatorRepresentative (H := H) μ),
      operatorFieldQuotient (H := H) μ (V : WeakOperatorRepresentative (H := H) μ) =
        (U : WeakOperatorField (H := H) μ) := by
  classical
  let R := representative (U : WeakOperatorField (H := H) μ)
  have hR : operatorFieldQuotient (H := H) μ R = (U : WeakOperatorField (H := H) μ) :=
    quotient_representative _
  have hleft : operatorFieldQuotient (H := H) μ (star R * R) = operatorFieldQuotient (H := H) μ 1 := by
    rw [map_mul, map_star, hR, Unitary.star_mul_self_of_mem U.property, map_one]
  have hright : operatorFieldQuotient (H := H) μ (R * star R) = operatorFieldQuotient (H := H) μ 1 := by
    rw [map_mul, map_star, hR, Unitary.mul_star_self_of_mem U.property, map_one]
  have hunit : ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval R x ∈ unitary (H →L[ℂ] H) := by
    filter_upwards [(operatorFieldQuotient_eq_iff μ _ _).mp hleft,
      (operatorFieldQuotient_eq_iff μ _ _).mp hright] with x hl hr
    exact ⟨hl, hr⟩
  let f : D → H →L[ℂ] H := fun x =>
    if WeakOperatorRepresentative.eval R x ∈ unitary (H →L[ℂ] H)
      then WeakOperatorRepresentative.eval R x else 1
  have hfunit (x : D) : f x ∈ unitary (H →L[ℂ] H) := by
    dsimp [f]
    split_ifs with hx
    · exact hx
    · exact (unitary (H →L[ℂ] H)).one_mem
  have heq : WeakOperatorRepresentative.eval R =ᵐ[μ] f :=
    hunit.mono fun x hx => by simp only [f, ite_eq_left hx]
  have hm (ξ : H) : AEStronglyMeasurable (fun x => f x ξ) μ :=
    (WeakOperatorRepresentative.eval_aestronglyMeasurable R ξ).congr
      (heq.mono fun _ h => congrArg (fun T => T ξ) h)
  have hs (ξ : H) : AEStronglyMeasurable (fun x => star (f x) ξ) μ :=
    (WeakOperatorRepresentative.star_eval_aestronglyMeasurable R ξ).congr
      (heq.mono fun _ h => congrArg (fun T : H →L[ℂ] H => star T ξ) h)
  have hn (x : D) : ‖f x‖ ≤ 1 := norm_unitary_le_one ⟨f x, hfunit x⟩
  let F : WeakOperatorRepresentative (H := H) μ := WeakOperatorRepresentative.mk f 1 hn hm hs
  have hFU : F ∈ unitary (WeakOperatorRepresentative (H := H) μ) := by
    constructor
    · apply Subtype.ext
      apply BoundedContinuousFunction.ext
      intro x
      exact (hfunit x.ofTopology).1
    · apply Subtype.ext
      apply BoundedContinuousFunction.ext
      intro x
      exact (hfunit x.ofTopology).2
  refine ⟨⟨F, hFU⟩, ?_⟩
  exact ((operatorFieldQuotient_eq_iff μ R F).mpr heq).symm.trans hR

end WeakOperatorField

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
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableOperatorCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable unitary cocycles from the quotient construction -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [DiscreteTopology G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- A quotient-valued cocycle admits measurable, everywhere unitary values.
The cocycle identities and norm bound hold almost everywhere. -/
theorem exists_measurable_operator_cocycle_with_lift_oai
    (α : NonsingularAction G D μ)
    (V W : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hW : ∀ g h, W.val g * α.operatorAction (H := H) g (W.val h) = W.val (g * h))
    {r : ℝ} (hclose : dist V W ≤ r) :
    ∃ U : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (U g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ g, ∀ᵐ x ∂μ,
        ‖(U g x : H →L[ℂ] H) -
          WeakOperatorRepresentative.eval (WeakOperatorField.representative (V.val g)) x‖ ≤ r) ∧
      (∀ g, ∀ᵐ x ∂μ, (U g x : H →L[ℂ] H) =
        WeakOperatorRepresentative.eval (WeakOperatorField.representative (W.val g)) x) := by
  classical
  choose R hR using fun g => WeakOperatorField.exists_unitary_lift (unitaryFamilyEval W g)
  let U : G → D → unitary (H →L[ℂ] H) :=
    fun g => WeakOperatorRepresentative.unitaryEval (R g)
  refine ⟨U, fun g ξ => WeakOperatorRepresentative.unitaryEval_measurable (R g) ξ, ?_, ?_, ?_⟩
  · intro g h
    have hquot : operatorFieldQuotient (H := H) μ
        ((R g : WeakOperatorRepresentative (H := H) μ) *
          WeakOperatorRepresentative.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (R h)) =
        operatorFieldQuotient (H := H) μ (R (g * h)) := by
      rw [map_mul, ← WeakOperatorField.pullback_quotient, hR g, hR h, hR (g * h)]
      exact hW g h
    exact (operatorFieldQuotient_eq_iff μ _ _).mp hquot
  · intro g
    let F := (R g : WeakOperatorRepresentative (H := H) μ) -
      WeakOperatorField.representative (V.val g)
    have hnorm : ‖operatorFieldQuotient (H := H) μ F‖ ≤ r := by
      have hg := (V.val - W.val).norm_coe_le_norm g
      have hd : ‖V.val - W.val‖ ≤ r := by
        simpa only [Subtype.dist_eq, dist_eq_norm] using hclose
      calc
        ‖operatorFieldQuotient (H := H) μ F‖ = ‖W.val g - V.val g‖ := by
          rw [map_sub, hR g, WeakOperatorField.quotient_representative]
          rfl
        _ = ‖V.val g - W.val g‖ := norm_sub_rev _ _
        _ ≤ ‖V.val - W.val‖ := hg
        _ ≤ r := hd
    filter_upwards [operatorField_ae_norm_le F] with x hx
    exact hx.trans hnorm

  · intro g
    exact (operatorFieldQuotient_eq_iff μ _ _).mp
      ((hR g).trans (WeakOperatorField.quotient_representative (W.val g)).symm)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_measurable_operator_cocycle_with_lift_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_measurable_operator_cocycle_with_lift_oai.{u_1, u_2, u_3}
