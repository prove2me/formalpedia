-- Prove2me | solution 1 for OAI.KadisonKastler.scalarCenter_spatialProduct_of_local_swaps
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:26:22.430438+00:00
-- url     : https://prove2.me/submissions/f695311e-c7cd-4f3b-81e6-e3a351f79914

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
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
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
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
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
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
import Definitions.Def_Q260K019
import Definitions.Def_Q260K029

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The centralizer of an infinite product state is irreducible

The proof uses only dense local vectors and state-preserving local swaps
which move a local observable to an independent set of sites. These are
the finite-site properties of the two-ratio tensor product in section 6.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_productVectorState_le (Ω : H) (hΩ : ‖Ω‖ = 1) (T : H →L[ℂ] H) :
    ‖productVectorState Ω T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg Ω)
    _ = ‖T‖ := by rw [hΩ]; ring

/-- State centralization and commutation with `x` allow a local observable
to be moved by the swap while leaving its pairing with `x` unchanged. -/
theorem productVectorState_swap (D : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ D)
    (hcentral : ProductStateCentralizes D Ω u)
    (a x : H →L[ℂ] H) (ha : a ∈ D) (hx : x ∈ D)
    (hcomm : (u : H →L[ℂ] H) * x = x * u) :
    productVectorState Ω (unitaryConj u a * x) = productVectorState Ω (a * x) := by
  have hxu : star (u : H →L[ℂ] H) * x * u = x := by
    calc
      _ = star (u : H →L[ℂ] H) * (x * u) := mul_assoc _ _ _
      _ = star (u : H →L[ℂ] H) * (u * x) := by rw [← hcomm]
      _ = x := by rw [← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]
  calc
    _ = productVectorState Ω ((u : H →L[ℂ] H) * (a * star (u : H →L[ℂ] H) * x)) := by
      simp only [unitaryConj, mul_assoc]
    _ = productVectorState Ω ((a * star (u : H →L[ℂ] H) * x) * u) :=
      hcentral _ (D.mul_mem (D.mul_mem ha (D.toStarSubalgebra.star_mem' hu)) hx)
    _ = productVectorState Ω (a * x) := by rw [mul_assoc a, mul_assoc a, hxu]

omit [CompleteSpace H] in
/-- A vector-functional error only sees the vector error in the right factor. -/
theorem productVectorState_mul_error (Ω : H) (hΩ : ‖Ω‖ = 1)
    (a x y : H →L[ℂ] H) :
    ‖productVectorState Ω (a * x) - productVectorState Ω (a * y)‖ ≤
      ‖a‖ * ‖(x - y) Ω‖ := by
  calc
    _ = ‖inner ℂ Ω (a ((x - y) Ω))‖ := by
      simp only [productVectorState, mul_apply_eq_comp, sub_apply, map_sub, inner_sub_right]
    _ ≤ ‖Ω‖ * ‖a ((x - y) Ω)‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖a‖ * ‖(x - y) Ω‖) :=
      mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg Ω)
    _ = ‖a‖ * ‖(x - y) Ω‖ := by rw [hΩ, one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateIrreducible
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local independent swaps force scalar relative commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace LocalProductSwaps

variable {D : VonNeumannAlgebra H} {Ω : H} (L : LocalProductSwaps D Ω)

/-- Factorization of the vector state against every local observable. -/
theorem local_factorization (hΩ : ‖Ω‖ = 1) (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u)
    (k : ℕ) (a : L.localAlgebra k) :
    productVectorState Ω ((a : H →L[ℂ] H) * x) =
      productVectorState Ω a * productVectorState Ω x := by
  apply eq_of_sub_eq_zero
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let δ := ε / (2 * ‖(a : H →L[ℂ] H)‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp (L.dense (x Ω)) δ hδ
  have herr : ‖(x - (p.2 : H →L[ℂ] H)) Ω‖ < δ := by
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using hp
  obtain ⟨u, hu, hc, hi⟩ := L.independent_swap k a p.1
  let b : H →L[ℂ] H := p.2
  let c : H →L[ℂ] H := unitaryConj u a
  have hs : productVectorState Ω (c * x) = productVectorState Ω (a * x) :=
    productVectorState_swap D Ω u hu hc a x (L.local_le k a.property) hx (hcomm u hu hc)
  have hi' : productVectorState Ω (c * b) =
      productVectorState Ω a * productVectorState Ω b := hi p.2
  have he : productVectorState Ω (a * x) -
      productVectorState Ω a * productVectorState Ω x =
      (productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x) := by
    rw [hs, hi']
    ring
  have hv : ‖productVectorState Ω b - productVectorState Ω x‖ ≤ ‖(x - b) Ω‖ := by
    calc
      _ = ‖inner ℂ Ω ((b - x) Ω)‖ := by
        simp only [productVectorState, sub_apply, inner_sub_right]
      _ ≤ ‖Ω‖ * ‖(b - x) Ω‖ := norm_inner_le_norm _ _
      _ = ‖(x - b) Ω‖ := by rw [hΩ, one_mul, sub_apply, norm_sub_rev, ← sub_apply]
  apply le_of_lt
  calc
    _ = ‖(productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      congrArg norm he
    _ ≤ ‖productVectorState Ω (c * x) - productVectorState Ω (c * b)‖ +
        ‖productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      norm_add_le _ _
    _ ≤ ‖c‖ * ‖(x - b) Ω‖ + ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      apply add_le_add (productVectorState_mul_error Ω hΩ c x b)
      rw [norm_mul]
      exact mul_le_mul (norm_productVectorState_le Ω hΩ a) hv (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      dsimp [c]
      rw [norm_unitaryConj]
      ring
    _ ≤ (2 * ‖(a : H →L[ℂ] H)‖ + 1) * ‖(x - b) Ω‖ := by
      nlinarith [norm_nonneg ((x - b) Ω)]
    _ < (2 * ‖(a : H →L[ℂ] H)‖ + 1) * δ :=
      mul_lt_mul_of_pos_left herr (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

include L in
/-- The relative commutant of the full vector-state centralizer is scalar.
The argument uses only finite-site independence, dense local vectors, and
separation by the product vector. -/
theorem scalar_of_commutes (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState Ω x • (1 : H →L[ℂ] H) := by
  have hv : x Ω = productVectorState Ω x • Ω := by
    apply DenseRange.eq_of_inner_right ℂ L.dense
    rintro ⟨k, a⟩
    have hf := L.local_factorization hΩ x hx hcomm k (star a)
    calc
      inner ℂ ((a : H →L[ℂ] H) Ω) (x Ω) =
          productVectorState Ω ((star (a : H →L[ℂ] H)) * x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        rfl
      _ = productVectorState Ω (star (a : H →L[ℂ] H)) * productVectorState Ω x := hf
      _ = inner ℂ ((a : H →L[ℂ] H) Ω) (productVectorState Ω x • Ω) := by
        rw [inner_smul_right]
        change inner ℂ Ω ((a : H →L[ℂ] H).adjoint Ω) * productVectorState Ω x = _
        rw [ContinuousLinearMap.adjoint_inner_right]
        ring
  have he : (⟨x, hx⟩ : Algebra D) =
      ⟨productVectorState Ω x • (1 : H →L[ℂ] H),
        D.toStarSubalgebra.smul_mem D.one_mem _⟩ := by
    apply hsep
    simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk, smul_apply,
      one_apply_eq_self] using hv
  exact congrArg Subtype.val he

end LocalProductSwaps

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialProduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.leftTensorVector_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.rightTensorSlice_apply _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.tensorVectorSliceCP_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete spatial tensor product used in the fixed-factor reduction

The spatial von Neumann algebra is the bicommutant of the bounded tensor
operators. Vector slices act on the completed tensor Hilbert space.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- Slicing a simple tensor gives its actual vector-state coefficient. -/
theorem tensorVectorSlice_tensor (ξ : K) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    tensorVectorSlice ξ (spatialTensorOp S T) = (inner ℂ ξ (T ξ)) • S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [tensorVectorSlice_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul, smul_apply,
    inner_smul_right]
  ring

/-- A unit vector makes the slice a left inverse of the first-leg inclusion. -/
theorem tensorVectorSlice_spatialLeft (ξ : K) (hξ : ‖ξ‖ = 1) (S : H →L[ℂ] H) :
    tensorVectorSlice ξ (spatialLeft S) = S := by
  change tensorVectorSlice ξ (spatialTensorOp S 1) = S
  rw [tensorVectorSlice_tensor, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialRightSlice
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Right-leg slices and the relative commutant of a product centralizer -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialRight_leftTensorVector (ξ : H) (b : K →L[ℂ] K) :
    spatialRight b ∘L leftTensorVector ξ = leftTensorVector ξ ∘L b := by
  ext η
  simp only [ContinuousLinearMap.comp_apply, leftTensorVector_apply]
  exact spatialTensorOp_coe 1 b (ξ ⊗ₜ[ℂ] η)

theorem leftTensorVector_adjoint_spatialRight (ξ : H) (b : K →L[ℂ] K) :
    (leftTensorVector ξ).adjoint ∘L spatialRight b = b ∘L (leftTensorVector ξ).adjoint := by
  have he := congrArg (fun L : K →L[ℂ] SpatialHilbert H K => L.adjoint)
    (spatialRight_leftTensorVector ξ (star b))
  have hs : (spatialRight (H := H) (K := K) (star b)).adjoint =
      spatialRight (H := H) (K := K) b := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
  have hb : (star b).adjoint = b := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star]
  simpa only [ContinuousLinearMap.adjoint_comp, hs, hb] using he

/-- Right-leg compression intertwines any second-leg operator commuting
with the operator being compressed. -/
theorem rightTensorSlice_commute (ξ : H)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (b : K →L[ℂ] K)
    (hc : spatialRight b * T = T * spatialRight b) :
    b * rightTensorSlice ξ T = rightTensorSlice ξ T * b := by
  have hV := spatialRight_leftTensorVector ξ b
  have hVs := leftTensorVector_adjoint_spatialRight ξ b
  ext η
  have hVη := congrArg (fun L : K →L[ℂ] SpatialHilbert H K => L η) hV
  have hVsη := congrArg (fun L : SpatialHilbert H K →L[ℂ] K =>
    L (T (leftTensorVector ξ η))) hVs
  have hcη := congrArg (fun L : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    L (leftTensorVector ξ η)) hc
  change b ((leftTensorVector ξ).adjoint (T (leftTensorVector ξ η))) =
    (leftTensorVector ξ).adjoint (T (leftTensorVector ξ (b η)))
  change (leftTensorVector ξ).adjoint (spatialRight b (T (leftTensorVector ξ η))) =
    b ((leftTensorVector ξ).adjoint (T (leftTensorVector ξ η))) at hVsη
  change spatialRight b (T (leftTensorVector ξ η)) =
    T (spatialRight b (leftTensorVector ξ η)) at hcη
  rw [← hVsη, hcη]
  change spatialRight b (leftTensorVector ξ η) = leftTensorVector ξ (b η) at hVη
  rw [hVη]

/-- Slicing the actual spatial product lands in its second algebra. -/
theorem rightTensorSlice_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (ξ : H) (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D) : rightTensorSlice ξ T ∈ D := by
  rw [← D.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  exact rightTensorSlice_commute ξ T b (spatialRight_commutes_product M D b hb T hT)

/-- Irreducibility of the product-state centralizer scalarizes every
right-leg compression of an operator in its spatial relative commutant. -/
theorem rightTensorSlice_scalar_of_local_swaps
    (M : VonNeumannAlgebra H) {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D)
    (hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → spatialRight (u : K →L[ℂ] K) * T =
        T * spatialRight (u : K →L[ℂ] K)) (ξ : H) :
    ∃ z : ℂ, rightTensorSlice ξ T = z • (1 : K →L[ℂ] K) := by
  refine ⟨productVectorState Ω (rightTensorSlice ξ T),
    L.scalar_of_commutes hΩ hsep _ (rightTensorSlice_mem M D ξ T hT) ?_⟩
  intro u hu hc
  exact rightTensorSlice_commute ξ T u (hcomm u hu hc)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialSliceRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the first tensor leg from scalar opposite slices

Polarization proves the relative-commutant identity needed for the fixed
product factor. No spatial tensor commutation theorem is added as an input.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
private theorem operator_eq_of_diagonal {S T : H →L[ℂ] H}
    (h : ∀ x, inner ℂ x (S x) = inner ℂ x (T x)) : S = T := by
  have he : S.toLinearMap = T.toLinearMap := (ext_inner_map _ _).mp (fun x => by
    exact (inner_conj_symm (S x) x).symm.trans
      ((congrArg (starRingEnd ℂ) (h x)).trans (inner_conj_symm (T x) x)))
  ext x
  exact congrArg (fun L : H →ₗ[ℂ] H => L x) he

/-- Scalar right-leg slices force an operator to lie entirely in the first leg. -/
theorem spatial_eq_left_of_scalar_right_slices
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (Ω : K) (hΩ : ‖Ω‖ = 1)
    (hscalar : ∀ x : H, ∃ z : ℂ, rightTensorSlice x T = z • (1 : K →L[ℂ] K)) :
    T = spatialLeft (K := K) (tensorVectorSlice Ω T) := by
  let A : H →L[ℂ] H := tensorVectorSlice Ω T
  have hcross (η ζ : K) :
      (tensorVector η).adjoint ∘L T ∘L tensorVector ζ = inner ℂ η ζ • A := by
    apply operator_eq_of_diagonal
    intro x
    obtain ⟨z, hz⟩ := hscalar x
    have hηζ : inner ℂ (tensorVector η x) (T (tensorVector ζ x)) =
        inner ℂ η (rightTensorSlice x T ζ) := by
      rw [rightTensorSlice_apply, ContinuousLinearMap.adjoint_inner_right]
      rfl
    have hA : inner ℂ x (A x) = z := by
      change inner ℂ x ((tensorVector Ω).adjoint (T (tensorVector Ω x))) = z
      rw [ContinuousLinearMap.adjoint_inner_right]
      rw [show inner ℂ (tensorVector Ω x) (T (tensorVector Ω x)) =
        inner ℂ Ω (rightTensorSlice x T Ω) by
          rw [rightTensorSlice_apply, ContinuousLinearMap.adjoint_inner_right]; rfl]
      rw [hz]
      simp only [smul_apply, one_apply_eq_self, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hΩ, one_pow, RCLike.ofReal_one, mul_one]
    change inner ℂ x ((tensorVector η).adjoint (T (tensorVector ζ x))) =
      inner ℂ x ((inner ℂ η ζ) • (A x))
    rw [ContinuousLinearMap.adjoint_inner_right, hηζ, hz, inner_smul_right, hA]
    simp only [smul_apply, one_apply_eq_self, inner_smul_right]
    ring
  apply spatialTensorOp_ext
  intro x ζ
  apply spatialTensor_vector_ext
  intro y η
  have he := congrArg (fun B : H →L[ℂ] H => inner ℂ y (B x)) (hcross η ζ)
  change inner ℂ y ((tensorVector η).adjoint (T (tensorVector ζ x))) = _ at he
  rw [ContinuousLinearMap.adjoint_inner_right] at he
  change inner ℂ (tensorVector η y) (T (tensorVector ζ x)) = _
  rw [he]
  change inner ℂ y ((inner ℂ η ζ) • (A x)) =
    inner ℂ (tensorVector η y) (spatialTensorOp A 1 (tensorVector ζ x))
  simp only [tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    one_apply_eq_self, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul,
    inner_smul_right]
  ring

/-- The first-leg relative-commutant identity for the product-state
centralizer follows from local swaps and concrete vector slices. -/
theorem spatial_relative_commutant_of_local_swaps
    (M : VonNeumannAlgebra H) {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D)
    (hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → spatialRight (u : K →L[ℂ] K) * T =
        T * spatialRight (u : K →L[ℂ] K)) :
    ∃ a ∈ M, T = spatialLeft (K := K) a := by
  refine ⟨tensorVectorSlice Ω T, tensorVectorSlice_mem M D Ω T hT, ?_⟩
  exact spatial_eq_left_of_scalar_right_slices T Ω hΩ
    (rightTensorSlice_scalar_of_local_swaps M L hΩ hsep T hT hcomm)


/-- Tensoring a factor with the product algebra remains factorial. This
uses the proved relative-commutant identity rather than a tensor-factor
classification assumption. -/
theorem scalarCenter_spatialProduct_of_local_swaps_oai
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω)) :
    ScalarCenter (spatialProductAlgebra M D) := by
  intro T hT hcentral
  obtain ⟨a, ha, rfl⟩ := spatial_relative_commutant_of_local_swaps M L hΩ hsep T hT
    (fun u hu _ => hcentral _ (spatialRight_mem_product M D hu))
  have hac : ∀ x ∈ M, x * a = a * x := by
    intro x hx
    have he := hcentral _ (spatialLeft_mem_product M D hx)
    change spatialLeft (K := K) x * spatialLeft (K := K) a =
      spatialLeft (K := K) a * spatialLeft (K := K) x at he
    rw [← map_mul, ← map_mul] at he
    have hs := congrArg (tensorVectorSlice Ω) he
    simpa only [tensorVectorSlice_spatialLeft Ω hΩ] using hs
  obtain ⟨z, hz⟩ := hM a ha hac
  refine ⟨z, ?_⟩
  rw [hz, map_smul, map_one]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.scalarCenter_spatialProduct_of_local_swaps_oai.{u_1, u_2} := @OAI.KadisonKastler.scalarCenter_spatialProduct_of_local_swaps_oai.{u_1, u_2}
