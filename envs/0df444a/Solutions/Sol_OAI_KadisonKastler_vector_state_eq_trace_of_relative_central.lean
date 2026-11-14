-- Prove2me | solution 1 for OAI.KadisonKastler.vector_state_eq_trace_of_relative_central
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:17:15.875038+00:00
-- url     : https://prove2.me/submissions/fd95c744-b4a3-4e43-bc56-fac4bc455eb8

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K029

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConj_sub (v : unitary (H →L[ℂ] H)) (x y : H →L[ℂ] H) :
    unitaryConj v (x - y) = unitaryConj v x - unitaryConj v y := by
  simp [unitaryConj, mul_sub, sub_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompactHilbertCenter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unique centers of compact convex Hilbert images

Only compactness for the lower semicontinuous squared distances is used.
This form applies directly to weak operator compact sets of implementers.
-/

namespace KadisonKastler

noncomputable section

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A compact family whose Hilbert image is bounded and midpoint convex
has a unique image minimizing its squared covering radius. -/
theorem exists_unique_compact_hilbert_center
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) (v : X → E)
    (hdist : ∀ y, LowerSemicontinuous (fun x => ‖v x - y‖ ^ 2))
    (hmid : ∀ x ∈ K, ∀ y ∈ K,
      ∃ z ∈ K, v z = (1 / 2 : ℝ) • (v x + v y))
    (C : ℝ) (hC : ∀ x ∈ K, ‖v x‖ ≤ C) :
    ∃ x ∈ K, ∀ y ∈ K,
      (∀ z ∈ K, ‖v y - v z‖ ^ 2 ≤ ⨆ w : K, ‖v x - v w‖ ^ 2) → v y = v x := by
  classical
  let : Nonempty K := hne.to_subtype
  let R (x : X) : ℝ := ⨆ y : K, ‖v x - v y‖ ^ 2
  have hb (x : X) : BddAbove (Set.range (fun y : K => ‖v x - v y‖ ^ 2)) := by
    refine ⟨(‖v x‖ + C) ^ 2, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg (v x - v y))
      ((norm_sub_le (v x) (v y)).trans (by linarith [hC y y.property])) 2
  have hR : LowerSemicontinuous R :=
    lowerSemicontinuous_ciSup hb (fun y => hdist (v y))
  obtain ⟨x, hx, hm⟩ := (hR.lowerSemicontinuousOn K).exists_isMinOn hne hK
  have hmin := isMinOn_iff.mp hm
  have hle (a : X) (b : K) : ‖v a - v b‖ ^ 2 ≤ R a := le_ciSup (hb a) b
  refine ⟨x, hx, ?_⟩
  intro y hy hyr
  obtain ⟨z, hz, he⟩ := hmid x hx y hy
  have hupper : R z ≤ R x - ‖v x - v y‖ ^ 2 / 4 := by
    apply ciSup_le
    intro w
    have hp := parallelogram_law_with_norm ℂ (v x - v w) (v y - v w)
    have headd : (v x - v w) + (v y - v w) = (2 : ℝ) • (v z - v w) := by
      rw [he]
      module
    have hesub : (v x - v w) - (v y - v w) = v x - v y := by abel
    rw [headd, hesub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hp
    have hwx := hle x w
    have hwy := hyr w w.property
    nlinarith
  have hzm : R x ≤ R z := hmin z hz
  have hn : ‖v x - v y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v x - v y‖]
  have hh : v x - v y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact (sub_eq_zero.mp hh).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompactHilbertFixedPoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed points for compact families with an invariant Hilbert metric -/

namespace KadisonKastler

noncomputable section

variable {X E G : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_fixed_of_compact_hilbert_image
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) (v : X → E)
    (hdist : ∀ y, LowerSemicontinuous (fun x => ‖v x - y‖ ^ 2))
    (hmid : ∀ x ∈ K, ∀ y ∈ K, ∃ z ∈ K, v z = (1 / 2 : ℝ) • (v x + v y))
    (C : ℝ) (hC : ∀ x ∈ K, ‖v x‖ ≤ C) (hfaith : Set.InjOn v K)
    (F : G → X → X) (hmap : ∀ g x, x ∈ K → F g x ∈ K)
    (honto : ∀ g y, y ∈ K → ∃ z ∈ K, F g z = y)
    (hiso : ∀ g x, x ∈ K → ∀ y, y ∈ K →
      ‖v (F g x) - v (F g y)‖ = ‖v x - v y‖) :
    ∃ x ∈ K, ∀ g, F g x = x := by
  obtain ⟨x, hx, hc⟩ := exists_unique_compact_hilbert_center K hK hne v hdist hmid C hC
  refine ⟨x, hx, ?_⟩
  intro g
  apply hfaith (hmap g x hx) hx
  apply hc (F g x) (hmap g x hx)
  intro z hz
  obtain ⟨w, hw, rfl⟩ := honto g z hz
  rw [hiso g x hx w hw]
  have hb : BddAbove (Set.range (fun y : K => ‖v x - v y‖ ^ 2)) := by
    refine ⟨(2 * C) ^ 2, ?_⟩
    rintro _ ⟨y, rfl⟩
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by linarith [hC x hx, hC y y.property])
  exact le_ciSup hb (⟨w, hw⟩ : K)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WOTVectorLowerSemicontinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Lower semicontinuity of vector distances in the weak operator topology -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_vector_sqDistance_lowerSemicontinuous (ξ η : H) :
    LowerSemicontinuous (fun T : H →WOT[ℂ] H => ‖T ξ - η‖ ^ 2) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  change IsClosed {T : H →WOT[ℂ] H | ‖T ξ - η‖ ^ 2 ≤ r}
  by_cases hr : 0 ≤ r
  · have he : {T : H →WOT[ℂ] H | ‖T ξ - η‖ ^ 2 ≤ r} =
        {T | ∀ ζ : H, ‖inner ℂ ζ (T ξ - η)‖ ^ 2 ≤ r * ‖ζ‖ ^ 2} := by
      ext T
      constructor
      · intro h ζ
        calc
          ‖inner ℂ ζ (T ξ - η)‖ ^ 2 ≤ (‖ζ‖ * ‖T ξ - η‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
          _ ≤ r * ‖ζ‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ‖ζ‖)]
      · intro h
        have hh := h (T ξ - η)
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)] at hh
        change ‖T ξ - η‖ ^ 2 ≤ r
        by_cases hn : ‖T ξ - η‖ = 0
        · simpa only [hn, zero_pow (by decide : 2 ≠ 0)] using hr
        · apply (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero hn)).mp
          simpa only [pow_two, mul_comm] using hh
    rw [he]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro ζ
    have hc : Continuous (fun T : H →WOT[ℂ] H => inner ℂ ζ (T ξ)) :=
      continuous_inner_apply continuous_id ξ ζ
    have hn : Continuous (fun T : H →WOT[ℂ] H =>
        ‖inner ℂ ζ (T ξ - η)‖) := by
      simpa only [inner_sub_right, Pi.sub_apply] using (hc.sub continuous_const).norm
    have hs : Continuous (fun T : H →WOT[ℂ] H =>
        ‖inner ℂ ζ (T ξ - η)‖ ^ 2) := by
      convert hn.mul hn using 1
      all_goals try with_reducible_and_instances rfl
      ext T
      simp only [Pi.mul_apply, pow_two]
    exact isClosed_le hs continuous_const
  · have he : {T : H →WOT[ℂ] H | ‖T ξ - η‖ ^ 2 ≤ r} = ∅ := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hr) (sq_nonneg _))
    rw [he]
    exact isClosed_empty

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalTracialSpatialSplit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting the tracial splitting argument through a normal representation -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem mem_of_fixed_commutant_unitaries (M : VonNeumannAlgebra H)
    (S : H →L[ℂ] H)
    (hfix : ∀ w : unitary (Algebra M.commutant),
      unitaryConj (ambientAlgebraUnitary w) S = S) : S ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  let L : Algebra M.commutant →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := fun b => b.val * S - S * b.val
      map_add' := by intro a b; simp only [AddMemClass.coe_add]; noncomm_ring
      map_smul' := by
        intro c b
        simp only [SetLike.val_smul, RingHom.id_apply, smul_mul_assoc, mul_smul_comm, smul_sub] }
  have hker : (⊤ : Submodule ℂ (Algebra M.commutant)) ≤ L.ker := by
    rw [← CStarAlgebra.span_unitary]
    apply Submodule.span_le.mpr
    intro b hb
    let w : unitary (Algebra M.commutant) := ⟨b, hb⟩
    have hh := congrArg (fun R : H →L[ℂ] H => R * b.val) (hfix w)
    change b.val * S * star b.val * b.val = S * b.val at hh
    have hstar : star b.val * b.val = 1 := congrArg Subtype.val w.property.1
    rw [mul_assoc, mul_assoc, hstar, mul_one] at hh
    exact sub_eq_zero.mpr hh
  intro b hb
  exact sub_eq_zero.mp (hker (show (⟨b, hb⟩ : Algebra M.commutant) ∈ ⊤ from trivial))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeTracialFixedPoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed points of relative unitary averaging in a finite algebra

The trace may be realized on a different Hilbert space. A bounded weakly
compact convex family invariant under the subalgebra's unitaries has a
fixed element, by the constructed compact Hilbert-center theorem.
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] in
theorem mem_commutant_of_unitaryConj_fixed (R : VonNeumannAlgebra H)
    (S : H →L[ℂ] H)
    (hfix : ∀ w : unitary (Algebra R),
      unitaryConj (ambientAlgebraUnitary w) S = S) : S ∈ R.commutant := by
  apply mem_of_fixed_commutant_unitaries R.commutant S
  rw [R.commutant_commutant]
  exact hfix

theorem exists_relative_tracial_fixed_point
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (P : VonNeumannAlgebra J)
    (ρ : Algebra M ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (K : Set (H →WOT[ℂ] H)) (hK : IsCompact K) (hne : K.Nonempty)
    (hKM : ∀ S ∈ K, S.toCLM ∈ M)
    (hmid : ∀ S ∈ K, ∀ V ∈ K, (1 / 2 : ℝ) • (S + V) ∈ K)
    (C : ℝ) (hbound : ∀ S ∈ K, ‖S.toCLM‖ ≤ C)
    (hinv : ∀ w : unitary (Algebra R), ∀ S ∈ K,
      ofCLM (unitaryConj (ambientAlgebraUnitary w) S.toCLM) ∈ K) :
    ∃ S ∈ K, ∀ w : unitary (Algebra R),
      unitaryConj (ambientAlgebraUnitary w) S.toCLM = S.toCLM := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let a (S : K) : Algebra M := ⟨S.val.toCLM, hKM S.val S.property⟩
  let L : Algebra M →ₗ[ℝ] J :=
    ((algebraVectorMap P τ.vector).comp ρ.toStarAlgHom.toLinearMap).restrictScalars ℝ
  let v (S : K) : J := L (a S)
  let B (S : K) : weakOperatorBall M C :=
    ⟨S.val, hKM S.val S.property, hbound S.val S.property⟩
  have hB : Continuous B := continuous_subtype_val.subtype_mk _
  have hv (η : J) : LowerSemicontinuous (fun S : K => ‖v S - η‖ ^ 2) := by
    have hc : Continuous (fun S : K => ofCLM (ρ (a S)).val) := (hρ C).comp hB
    change LowerSemicontinuous (fun S : K => ‖(ρ (a S)).val τ.vector - η‖ ^ 2)
    exact (wot_vector_sqDistance_lowerSemicontinuous (H := J) τ.vector η).comp hc
  have hn : (Set.univ : Set K).Nonempty := by
    obtain ⟨S, hS⟩ := hne
    exact ⟨⟨S, hS⟩, Set.mem_univ _⟩
  have hm (S : K) (_ : S ∈ Set.univ) (V : K) (_ : V ∈ Set.univ) :
      ∃ Z ∈ (Set.univ : Set K), v Z = (1 / 2 : ℝ) • (v S + v V) := by
    let Z : K := ⟨(1 / 2 : ℝ) • (S.val + V.val), hmid S.val S.property V.val V.property⟩
    refine ⟨Z, Set.mem_univ _, ?_⟩
    have he : a Z = (1 / 2 : ℝ) • (a S + a V) := Subtype.ext rfl
    change L (a Z) = _
    rw [he, L.map_smul, L.map_add]
  have hb (S : K) (_ : S ∈ Set.univ) : ‖v S‖ ≤ C :=
    (τ.norm₂_le_norm (ρ (a S))).trans
      ((NonUnitalStarAlgHom.norm_apply_le ρ.toStarAlgHom (a S)).trans (hbound S.val S.property))
  have hf : Set.InjOn v Set.univ := by
    intro S _ V _ he
    have hz : ρ (a S - a V) = 0 := by
      apply τ.separating
      change (ρ (a S - a V)).val τ.vector = 0
      rw [map_sub]
      exact sub_eq_zero.mpr he
    have haz : a S - a V = 0 := ρ.injective (hz.trans (map_zero ρ.toStarAlgHom).symm)
    apply Subtype.ext
    apply toCLM_injective
    exact congrArg Subtype.val (sub_eq_zero.mp haz)
  let F (w : unitary (Algebra R)) (S : K) : K :=
    ⟨ofCLM (unitaryConj (ambientAlgebraUnitary w) S.val.toCLM), hinv w S.val S.property⟩
  have ho (w : unitary (Algebra R)) (S : K) (_ : S ∈ Set.univ) :
      ∃ V ∈ (Set.univ : Set K), F w V = S := by
    refine ⟨F (star w) S, Set.mem_univ _, ?_⟩
    apply Subtype.ext
    apply toCLM_injective
    change unitaryConj (ambientAlgebraUnitary w)
      (unitaryConj (ambientAlgebraUnitary (star w)) S.val.toCLM) = S.val.toCLM
    have he : ambientAlgebraUnitary (star w) = star (ambientAlgebraUnitary w) :=
      Subtype.ext rfl
    rw [he]
    simpa only [star_star] using
      unitaryConj_star_unitaryConj (star (ambientAlgebraUnitary w)) S.val.toCLM
  have hi (w : unitary (Algebra R)) (S : K) (_ : S ∈ Set.univ)
      (V : K) (_ : V ∈ Set.univ) : ‖v (F w S) - v (F w V)‖ = ‖v S - v V‖ := by
    let wM : unitary (Algebra M) := Unitary.map
      (StarMonoidHom.ofClass (StarSubalgebra.inclusion hRM)) w
    let wP : unitary (Algebra P) := Unitary.map (StarMonoidHom.ofClass ρ.toStarAlgHom) wM
    have he : a (F w S) - a (F w V) =
        (wM : Algebra M) * (a S - a V) * star (wM : Algebra M) := by
      apply Subtype.ext
      change unitaryConj (ambientAlgebraUnitary w) S.val.toCLM -
        unitaryConj (ambientAlgebraUnitary w) V.val.toCLM = _
      exact (unitaryConj_sub (ambientAlgebraUnitary w) S.val.toCLM V.val.toCLM).symm
    change ‖L (a (F w S)) - L (a (F w V))‖ = ‖L (a S) - L (a V)‖
    rw [← L.map_sub, he, ← L.map_sub]
    change τ.norm₂ (ρ.toStarAlgHom ((wM : Algebra M) * (a S - a V) *
      star (wM : Algebra M))) = τ.norm₂ (ρ.toStarAlgHom (a S - a V))
    rw [map_mul, map_mul, map_star]
    exact conjugate_norm₂ τ wP (ρ (a S - a V))
  obtain ⟨S, _, hS⟩ := exists_fixed_of_compact_hilbert_image Set.univ isCompact_univ
    hn v hv hm C hb hf F (fun _ _ _ => Set.mem_univ _) ho hi
  exact ⟨S.val, S.property, fun w => congrArg (fun Z : K => Z.val.toCLM) (hS w)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeNormalFunctional
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normal functionals invariant under an irreducible finite inclusion

A compact slice of the operator ball preserves both a normal functional
and the trace. Relative tracial averaging makes an element of that slice
scalar, so the functional is its value at one times the trace.
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem normal_invariant_functional_eq_trace
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (P : VonNeumannAlgebra J)
    (ρ : Algebra M ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (φ : Algebra M →ₗ[ℂ] ℂ)
    (hφ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      φ ⟨b.val.toCLM, b.property.1⟩))
    (hinv : ∀ (w : unitary (Algebra R)) (a : Algebra M),
      φ ((coordinateInclusion hRM (w : Algebra R)) * a *
        star (coordinateInclusion hRM (w : Algebra R))) = φ a)
    (x : Algebra M) : φ x = τ.trace (ρ x) * φ 1 := by
  let ψ : Algebra M →ₗ[ℂ] ℂ := (innerSL ℂ τ.vector).toLinearMap.comp
    ((algebraVectorMap P τ.vector).comp ρ.toStarAlgHom.toLinearMap)
  have hψ (a : Algebra M) : ψ a = τ.trace (ρ a) := rfl
  have hcψ (C : ℝ) : Continuous (fun b : weakOperatorBall M C =>
      ψ ⟨b.val.toCLM, b.property.1⟩) :=
    continuous_inner_apply (hρ C) τ.vector τ.vector
  let : CompactSpace (weakOperatorBall M ‖x‖) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M ‖x‖)
  let L : Set (weakOperatorBall M ‖x‖) := {b |
    φ ⟨b.val.toCLM, b.property.1⟩ = φ x ∧ ψ ⟨b.val.toCLM, b.property.1⟩ = ψ x}
  have hLc : IsClosed L :=
    (isClosed_eq (hφ ‖x‖) continuous_const).inter (isClosed_eq (hcψ ‖x‖) continuous_const)
  let K : Set (H →WOT[ℂ] H) := Subtype.val '' L
  have hK : IsCompact K := hLc.isCompact.image continuous_subtype_val
  have hn : K.Nonempty := by
    refine ⟨ofCLM x.val, ?_⟩
    exact ⟨⟨ofCLM x.val, x.property, le_rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  have hk (S : H →WOT[ℂ] H) (hS : S ∈ K) :
      ∃ h : S ∈ weakOperatorBall M ‖x‖,
        φ ⟨S.toCLM, h.1⟩ = φ x ∧ ψ ⟨S.toCLM, h.1⟩ = ψ x := by
    obtain ⟨b, hb, rfl⟩ := hS
    exact ⟨b.property, hb⟩
  have hm (S) (hS : S ∈ K) : S.toCLM ∈ M := (hk S hS).choose.1
  have hb (S) (hS : S ∈ K) : ‖S.toCLM‖ ≤ ‖x‖ := (hk S hS).choose.2
  have hmid (S) (hS : S ∈ K) (V) (hV : V ∈ K) :
      (1 / 2 : ℝ) • (S + V) ∈ K := by
    obtain ⟨hs, hsφ, hsψ⟩ := hk S hS
    obtain ⟨hv, hvφ, hvψ⟩ := hk V hV
    let s : Algebra M := ⟨S.toCLM, hs.1⟩
    let v : Algebra M := ⟨V.toCLM, hv.1⟩
    let z : Algebra M := (1 / 2 : ℝ) • (s + v)
    have hz : ‖z‖ ≤ ‖x‖ := by
      calc
        ‖z‖ = (1 / 2 : ℝ) * ‖s + v‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (1 / 2 : ℝ) * (‖s‖ + ‖v‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ ‖x‖ := by change (1 / 2 : ℝ) * (‖S.toCLM‖ + ‖V.toCLM‖) ≤ ‖x‖; linarith [hs.2, hv.2]
    refine ⟨⟨ofCLM z.val, z.property, hz⟩, ?_, rfl⟩
    change φ z = φ x ∧ ψ z = ψ x
    constructor
    · change φ ((1 / 2 : ℝ) • (s + v)) = φ x
      rw [φ.map_smul_of_tower, φ.map_add, hsφ, hvφ]
      module
    · change ψ ((1 / 2 : ℝ) • (s + v)) = ψ x
      rw [ψ.map_smul_of_tower, ψ.map_add, hsψ, hvψ]
      module
  have hi (w : unitary (Algebra R)) (S) (hS : S ∈ K) :
      ofCLM (unitaryConj (ambientAlgebraUnitary w) S.toCLM) ∈ K := by
    obtain ⟨hs, hsφ, hsψ⟩ := hk S hS
    let s : Algebra M := ⟨S.toCLM, hs.1⟩
    let u : unitary (Algebra M) := Unitary.map
      (StarMonoidHom.ofClass (coordinateInclusion hRM)) w
    let z : Algebra M := (u : Algebra M) * s * star (u : Algebra M)
    have hz : ‖z‖ ≤ ‖x‖ := by
      change ‖unitaryConj (ambientAlgebraUnitary w) S.toCLM‖ ≤ ‖x‖
      rw [norm_unitaryConj]
      exact hs.2
    refine ⟨⟨ofCLM z.val, z.property, hz⟩, ?_, rfl⟩
    change φ z = φ x ∧ ψ z = ψ x
    constructor
    · exact (hinv w s).trans hsφ
    · rw [hψ]
      have hu : star (ρ.toStarAlgHom (u : Algebra M)) * ρ.toStarAlgHom (u : Algebra M) = 1 := by
        have h := congrArg ρ.toStarAlgHom u.property.1
        simpa only [map_mul, map_star, map_one] using h
      change τ.trace (ρ.toStarAlgHom ((u : Algebra M) * s * star (u : Algebra M))) = ψ x
      rw [map_mul, map_mul, map_star, τ.trace_mul_comm, ← mul_assoc,
        hu, one_mul]
      exact hsψ
  obtain ⟨S, hS, hfix⟩ := exists_relative_tracial_fixed_point M R hRM P ρ τ hρ
    K hK hn hm hmid ‖x‖ hb hi
  obtain ⟨hs, hsφ, hsψ⟩ := hk S hS
  let s : Algebra M := ⟨S.toCLM, hs.1⟩
  obtain ⟨c, hc⟩ := hirr s (mem_commutant_of_unitaryConj_fixed R S.toCLM hfix)
  have hψs : ψ s = c := by
    rw [hc, ψ.map_smul, hψ]
    simp only [map_one, TracialRepresentation.trace_one, smul_eq_mul, mul_one]
  have hφs : φ s = c * φ 1 := by rw [hc, φ.map_smul, smul_eq_mul]
  exact hsφ.symm.trans (hφs.trans (congrArg (fun t : ℂ => t * φ 1) (hψs.symm.trans hsψ)))

/-- A unit vector whose state is central over the irreducible subalgebra
implements the unique normalized trace. -/
theorem vector_state_eq_trace_of_relative_central_oai
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (P : VonNeumannAlgebra J)
    (ρ : Algebra M ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcentral : ∀ (r : Algebra R) (a : Algebra M),
      inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ))
    (x : Algebra M) : inner ℂ ξ (x.val ξ) = τ.trace (ρ x) := by
  let φ : Algebra M →ₗ[ℂ] ℂ :=
    (innerSL ℂ ξ).toLinearMap.comp (algebraVectorMap M ξ)
  have hc (C : ℝ) : Continuous (fun b : weakOperatorBall M C =>
      φ ⟨b.val.toCLM, b.property.1⟩) :=
    continuous_inner_apply continuous_subtype_val ξ ξ
  have hi (w : unitary (Algebra R)) (a : Algebra M) :
      φ (coordinateInclusion hRM (w : Algebra R) * a *
        star (coordinateInclusion hRM (w : Algebra R))) = φ a := by
    let b := coordinateInclusion hRM (w : Algebra R)
    have hu : star b * b = 1 := by
      have h := congrArg (coordinateInclusion hRM) w.property.1
      simpa only [map_mul, map_star, map_one] using h
    change φ (b * a * star b) = φ a
    calc
      φ (b * a * star b) = φ (b * (a * star b)) := congrArg φ (mul_assoc _ _ _)
      _ = φ ((a * star b) * b) := hcentral (w : Algebra R) (a * star b)
      _ = φ a := by rw [mul_assoc, hu, mul_one]
  have h := normal_invariant_functional_eq_trace M R hRM P ρ τ hρ hirr φ hc hi x
  have h1 : φ 1 = 1 := by
    change inner ℂ ξ ξ = 1
    rw [inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  rw [h1, mul_one] at h
  change inner ℂ ξ (x.val ξ) = _ at h
  exact h

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.vector_state_eq_trace_of_relative_central_oai.{u_1, u_2} := @OAI.KadisonKastler.vector_state_eq_trace_of_relative_central_oai.{u_1, u_2}
