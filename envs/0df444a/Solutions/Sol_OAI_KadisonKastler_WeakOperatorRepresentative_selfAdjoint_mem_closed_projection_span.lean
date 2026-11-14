-- Prove2me | solution 1 for OAI.KadisonKastler.WeakOperatorRepresentative.selfAdjoint_mem_closed_projection_span
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:07:35.714196+00:00
-- url     : https://prove2.me/submissions/6385626e-483d-4c56-95e2-252922f75298

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
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
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_WeakOperatorRepresentative_eval_positiveSupport
import Theorems.Thm_OAI_KadisonKastler_WeakOperatorRepresentative_ext_eval

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldProjectionDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.operatorFieldFamilyInclusion_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral step approximation of measurable fields

A common dyadic mesh is used for every point of the measure space.
Measurability of its finitely many projection fields follows inductively
from the constructed spectral support. The existing concrete spectral
interval estimate gives a uniform operator-norm error.
-/

namespace KadisonKastler

open MeasureTheory Generator.Tracial
open scoped Topology CStarAlgebra BigOperators

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.densityFieldOrder
local instance densityFieldPreorder_ra98f3f_1 : Preorder (WeakOperatorRepresentative (H := H) μ) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance densityFieldLE_ra98f3f_1 : LE (WeakOperatorRepresentative (H := H) μ) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance densityFieldStarOrder_ra98f3f_1 : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.densityTopStarOrder
private theorem projectionField_isStarProjection
    (p : D → H →L[ℂ] H) (hp : ∀ x, IsStarProjection (p x))
    (hm : ∀ ξ, AEStronglyMeasurable (fun x => p x ξ) μ) :
    IsStarProjection (projectionField p hp hm) := by
  constructor
  · apply ext_eval
    intro x
    exact (hp x).isIdempotentElem.eq
  · apply ext_eval
    intro x
    exact (hp x).isSelfAdjoint.star_eq

attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.densityTopOrder
attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.densityTopPreorder
attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.densityTopLE
private theorem spectral_level_measurable (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F)
    (I : ∀ x : D, SpectralInterval (topElement F x))
    (L U : ℝ) (hL : ∀ x, (I x).lo = L) (hU : ∀ x, (I x).hi = U)
    (hm : ∀ ξ, AEStronglyMeasurable (fun x => ((I x).proj.val.val) ξ) μ) :
    ∀ (n : ℕ) (i : DyadicIndex n), ∃ l u : ℝ,
      (∀ x, ((I x).level (topElement_isSelfAdjoint F hF x) n i).lo = l) ∧
      (∀ x, ((I x).level (topElement_isSelfAdjoint F hF x) n i).hi = u) ∧
      (∀ ξ, AEStronglyMeasurable
        (fun x => ((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.val.val ξ) μ) := by
  intro n
  induction n with
  | zero => intro i; exact ⟨L, U, hL, hU, hm⟩
  | succ n ih =>
    rintro ⟨i, b⟩
    obtain ⟨l, u, hl, hu, hm⟩ := ih i
    let J := fun x => (I x).level (topElement_isSelfAdjoint F hF x) n i
    let p := fun x => (J x).proj.val.val
    have hp (x : D) : IsStarProjection (p x) := (J x).proj.property.map
      (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
    let P := projectionField p hp hm
    have hP : IsStarProjection P := projectionField_isStarProjection p hp hm
    let m : ℝ := (l + u) / 2
    let Z := P * F * P - (m : ℂ) • P
    have hZ : IsSelfAdjoint Z := by
      change star (P * F * P - (m : ℂ) • P) = P * F * P - (m : ℂ) • P
      simp only [star_sub, star_mul, star_smul, hP.isSelfAdjoint.star_eq,
        hF.star_eq, Complex.star_def, Complex.conj_ofReal, mul_assoc]
    have hmZ (x : D) : topElement Z x = cornerSpectralShift (J x).proj
        (topElement F x) (J x).midpoint := by
      apply Subtype.ext
      change eval Z x = _
      have hmid : (J x).midpoint = m := by
        dsimp [SpectralInterval.midpoint, m, J]
        rw [hl x, hu x]
      rw [hmid]
      rfl
    have hhigh (x : D) : eval (positiveSupport Z) x = (J x).highProjection.val.val := by
      rw [eval_positiveSupport Z hZ x, hmZ x]
      rfl
    have hhighMeas (ξ : H) : AEStronglyMeasurable
        (fun x => (J x).highProjection.val.val ξ) μ := by
      simpa only [hhigh] using (positiveSupport Z).eval_aestronglyMeasurable ξ
    cases b
    · refine ⟨l, m, ?_, ?_, ?_⟩
      · intro x
        exact hl x
      · intro x
        change (J x).midpoint = m
        dsimp [SpectralInterval.midpoint, m, J]
        rw [hl x, hu x]
      · intro ξ
        have hh := (hm ξ).sub (hhighMeas ξ)
        exact hh
    · refine ⟨m, u, ?_, ?_, hhighMeas⟩
      · intro x
        change (J x).midpoint = m
        dsimp [SpectralInterval.midpoint, m, J]
        rw [hl x, hu x]
      · intro x
        exact hu x

/-- Every self-adjoint measurable field is uniformly approximated by
finite linear combinations of measurable projection fields. -/
theorem selfAdjoint_mem_closed_projection_span_oai (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) :
    F ∈ (Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
      IsStarProjection p}).topologicalClosure := by
  classical
  change F ∈ closure (Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
    IsStarProjection p} : Set _)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * ‖F‖) / ε)
  have hwidth : (2 * ‖F‖) / (2 : ℝ) ^ n < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have hpow : (n : ℝ) < (2 : ℝ) ^ n := by
      exact_mod_cast (show n < 2 ^ n from Nat.lt_two_pow_self)
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith [mul_lt_mul_of_pos_left hpow hε]
  let I := uniformInterval F hF
  have hmeas := spectral_level_measurable F hF I (-‖F‖) ‖F‖
    (fun _ => rfl) (fun _ => rfl)
    (fun ξ => by
      change AEStronglyMeasurable (fun _ : D => (1 : H →L[ℂ] H) ξ) μ
      simpa only [one_apply_eq_self] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : D => ξ) μ)) n
  choose l u hl hu hm using hmeas
  let p (i : DyadicIndex n) : D → H →L[ℂ] H := fun x =>
    ((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.val.val
  have hp (i : DyadicIndex n) (x : D) : IsStarProjection (p i x) :=
    (((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.property).map
      (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
  let Q (i : DyadicIndex n) := projectionField (p i) (hp i) (hm i)
  let Y : WeakOperatorRepresentative (H := H) μ := ∑ i, (l i : ℂ) • Q i
  have hY : Y ∈ Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
      IsStarProjection p} := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact projectionField_isStarProjection (p i) (hp i) (hm i)
  have heval (x : D) : eval Y x = ((I x).approximant (topElement_isSelfAdjoint F hF x) n).val := by
    change evalHom x (∑ i, (l i : ℂ) • Q i) = _
    simp only [map_sum, map_smul, evalHom_apply, SpectralInterval.approximant]
    change (∑ i, (l i : ℂ) • p i x) =
      (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
        (∑ i, (((I x).level (topElement_isSelfAdjoint F hF x) n i).lo : ℂ) •
          ((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.val)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change (l i : ℂ) • p i x =
      (((I x).level (topElement_isSelfAdjoint F hF x) n i).lo : ℂ) • p i x
    rw [hl i x]
  have hnorm : ‖F - Y‖ ≤ (2 * ‖F‖) / (2 : ℝ) ^ n := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖eval F x.ofTopology - eval Y x.ofTopology‖ ≤ _
    rw [heval]
    change ‖topElement F x.ofTopology -
      (I x.ofTopology).approximant (topElement_isSelfAdjoint F hF x.ofTopology) n‖ ≤ _
    have h := (I x.ofTopology).approximant_norm_error
      (topElement_isSelfAdjoint F hF x.ofTopology) n (neg_le_self (norm_nonneg F))
    simpa only [I, uniformInterval, one_mul, mul_one, sub_neg_eq_add, two_mul] using h
  exact ⟨Y, hY, by simpa only [dist_eq_norm] using hnorm.trans_lt hwidth⟩

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.WeakOperatorRepresentative.selfAdjoint_mem_closed_projection_span_oai.{u_1, u_2} := @OAI.KadisonKastler.WeakOperatorRepresentative.selfAdjoint_mem_closed_projection_span_oai.{u_1, u_2}
