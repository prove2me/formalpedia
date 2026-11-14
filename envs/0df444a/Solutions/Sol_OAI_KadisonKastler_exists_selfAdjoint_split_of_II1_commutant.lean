-- Prove2me | solution 1 for OAI.KadisonKastler.exists_selfAdjoint_split_of_II1_commutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:11:07.886205+00:00
-- url     : https://prove2.me/submissions/a1c62c37-cdd4-45f9-a5cc-02d4fea53a63

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
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K064

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
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianDerivationAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Abelian averaging of a spatial derivation implementer

A spatial derivation preserving a von Neumann algebra also preserves its
commutant. Averaging over any commuting unitary subgroup of the commutant
keeps the same derivation, preserves the norm bound, and makes the
implementer commute with that subgroup. This is the abelian averaging
step in the spatial splitting argument.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutator_mem_commutant_of_preserves
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M.commutant) :
    T * b - b * T ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hab := VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  have hDb := VonNeumannAlgebra.mem_commutant_iff.mp hb _ (hT a ha)
  calc
    a * (T * b - b * T) = (T * a) * b - a * b * T -
        ((T * a - a * T) * b) := by noncomm_ring
    _ = (T * a) * b - a * b * T - b * (T * a - a * T) := by rw [hDb]
    _ = T * (a * b) - b * T * a := by
      simp only [mul_sub, ← mul_assoc, ← hab]
      abel
    _ = (T * b - b * T) * a := by rw [hab]; noncomm_ring

theorem unitaryConj_sub_mem_commutant_of_preserves
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : u.val ∈ M.commutant) :
    unitaryConj u T - T ∈ M.commutant := by
  have hc := commutator_mem_commutant_of_preserves M T hT u.val hu
  have he : unitaryConj u T - T = -(T * u.val - u.val * T) * star u.val := by
    dsimp [unitaryConj]
    rw [neg_mul, sub_mul, mul_assoc T, Unitary.mul_star_self_of_mem u.property, mul_one]
    noncomm_ring
  rw [he]
  exact M.commutant.mul_mem (M.commutant.neg_mem hc)
    (M.commutant.toStarSubalgebra.star_mem' hu)

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
-- module Solutions.OAIQ075_KS.KadisonKastler_WOTDistanceSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak operator separation and operator-norm distance

A dual estimate on weak-operator continuous functionals annihilating a
closed subspace gives strict norm approximants in that subspace.
-/

namespace KadisonKastler

open scoped Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wotNormBall_compact (r : ℝ) : IsCompact (wotNormBall (H := H) r) := by
  let M : VonNeumannAlgebra H :=
    { toStarSubalgebra := StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      centralizer_centralizer' := Set.centralizer_centralizer_centralizer _ }
  have he : Generator.Tracial.weakOperatorBall M r = wotNormBall (H := H) r := by
    ext T
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change T.toCLM ∈ StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      simp [StarSubalgebra.mem_centralizer_iff]
  rw [← he]
  exact Generator.Tracial.weakOperatorBall_isCompact M r

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalSpatialImplementer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Minimum distance for bounded self-adjoint spatial implementers

The bounded family of self-adjoint implementers of the same derivation is
weak-operator compact. Its distance from the self-adjoint part of the
algebra is attained. This is the compactness step of Sakai's spatial
splitting argument (Ann. Math. 83 (1966), Lemma 2, p.274).
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_isSelfAdjoint_isClosed :
    IsClosed {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} := by
  have he : {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} = {T | star T = T} := by
    ext T
    constructor
    · intro h
      exact DFunLike.ext _ _ (fun x => congrArg (fun A : H →L[ℂ] H => A x) h.star_eq)
    · intro h
      exact ContinuousLinearMap.ext (fun x => congrArg (fun A : H →WOT[ℂ] H => A x) h)
  rw [he]
  exact isClosed_eq continuous_star continuous_id

theorem wot_vonNeumann_isClosed (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ M} := by
  have he : {T : H →WOT[ℂ] H | T.toCLM ∈ M} =
      {T | ∀ a : M.commutant.toStarSubalgebra, ∀ x y : H,
        inner ℂ (a.val.adjoint y) (T x) = inner ℂ y (T (a.val x))} := by
    ext T
    constructor
    · intro h a x y
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact congrArg (inner ℂ y) (congrArg (fun R : H →L[ℂ] H => R x)
        (VonNeumannAlgebra.mem_commutant_iff.mp a.property T.toCLM h).symm)
    · intro h
      rw [← VonNeumannAlgebra.commutant_commutant M]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro a ha
      ext x
      apply ext_inner_left ℂ
      intro y
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMapWOT.toCLM_apply] using
        h ⟨a, ha⟩ x y
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_eq (continuous_inner_apply continuous_id x (a.val.adjoint y))
      (continuous_inner_apply continuous_id (a.val x) y))))

theorem boundedSelfAdjointImplementers_compact (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) : IsCompact (boundedSelfAdjointImplementers M T) := by
  have hc : IsClosed {S : H →WOT[ℂ] H | S.toCLM - T ∈ M.commutant} :=
    (wot_vonNeumann_isClosed M.commutant).preimage
      (continuous_id.sub continuous_const)
  have he : boundedSelfAdjointImplementers M T =
      wotNormBall ‖T‖ ∩ {S | IsSelfAdjoint S.toCLM} ∩
        {S | S.toCLM - T ∈ M.commutant} := by
    ext S
    simp only [boundedSelfAdjointImplementers, wotNormBall, Set.mem_ofPred_eq,
      Set.mem_inter_iff]
    tauto
  rw [he]
  exact ((wotNormBall_compact ‖T‖).inter_right wot_isSelfAdjoint_isClosed).inter_right hc

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
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialSpatialGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Geometry of the bounded tracial implementer family -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Midpoints stay in the weakly compact family of implementers. -/
theorem boundedSelfAdjointImplementers_midpoint (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {S V : H →WOT[ℂ] H}
    (hS : S ∈ boundedSelfAdjointImplementers M T)
    (hV : V ∈ boundedSelfAdjointImplementers M T) :
    (1 / 2 : ℝ) • (S + V) ∈ boundedSelfAdjointImplementers M T := by
  refine ⟨?_, ?_, ?_⟩
  · change star ((1 / 2 : ℝ) • (S.toCLM + V.toCLM)) = _
    simp only [star_smul, star_trivial, star_add, hS.1.star_eq, hV.1.star_eq]
    rfl
  · change ‖(1 / 2 : ℝ) • (S.toCLM + V.toCLM)‖ ≤ ‖T‖
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hn := norm_add_le S.toCLM V.toCLM
    linarith [hS.2.1, hV.2.1]
  · have he : (1 / 2 : ℝ) • (S.toCLM + V.toCLM) - T =
        (1 / 2 : ℝ) • ((S.toCLM - T) + (V.toCLM - T)) := by module
    change (1 / 2 : ℝ) • (S.toCLM + V.toCLM) - T ∈ M.commutant
    rw [he]
    exact (M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem
      (M.commutant.add_mem hS.2.2 hV.2.2) _

/-- Conjugation by a commutant unitary preserves every defining constraint. -/
theorem boundedSelfAdjointImplementers_conjugate (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : u.val ∈ M.commutant)
    {S : H →L[ℂ] H} (hS : ofCLM S ∈ boundedSelfAdjointImplementers M T) :
    ofCLM (unitaryConj u S) ∈ boundedSelfAdjointImplementers M T := by
  refine ⟨?_, ?_, ?_⟩
  · change star (u.val * S * star u.val) = _
    simp only [star_mul, star_star, hS.1.star_eq, unitaryConj, mul_assoc]
  · simpa only [ofCLM_toCLM, norm_unitaryConj] using hS.2.1
  · have hd := unitaryConj_sub_mem_commutant_of_preserves M T hT u hu
    have hm : unitaryConj u (S - T) ∈ M.commutant :=
      M.commutant.mul_mem (M.commutant.mul_mem hu hS.2.2)
        (M.commutant.toStarSubalgebra.star_mem' hu)
    have he : unitaryConj u S - T =
        unitaryConj u (S - T) + (unitaryConj u T - T) := by
      rw [unitaryConj_sub]
      abel
    change unitaryConj u S - T ∈ M.commutant
    rw [he]
    exact M.commutant.add_mem hm hd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalTracialSpatialSplit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The trace vector may live in a different faithful normal representation. -/
theorem exists_selfAdjoint_split_of_normal_tracial_commutant
    (M : VonNeumannAlgebra H) (P : VonNeumannAlgebra J)
    (ρ : Algebra M.commutant ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M.commutant C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let K := boundedSelfAdjointImplementers M T
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    (boundedSelfAdjointImplementers_compact M T)
  let L : Algebra M.commutant →ₗ[ℝ] J :=
    ((algebraVectorMap P τ.vector).comp ρ.toStarAlgHom.toLinearMap).restrictScalars ℝ
  let a (S : K) : Algebra M.commutant := ⟨S.val.toCLM - T, S.property.2.2⟩
  let v (S : K) : J := L (a S)
  have han (S : K) : ‖a S‖ ≤ 2 * ‖T‖ := by
    exact (norm_sub_le S.val.toCLM T).trans (by linarith [S.property.2.1])
  let B (S : K) : weakOperatorBall M.commutant (2 * ‖T‖) :=
    ⟨ofCLM (a S).val, (a S).property, han S⟩
  have hB : Continuous B := by
    have hc : Continuous (fun S : K => S.val - ofCLM T) :=
      continuous_subtype_val.sub continuous_const
    apply Continuous.subtype_mk
    change Continuous (fun S : K => S.val - ofCLM T)
    exact hc
  have hv (η : J) : LowerSemicontinuous (fun S : K => ‖v S - η‖ ^ 2) := by
    have hc : Continuous (fun S : K => ofCLM (ρ (a S)).val) :=
      (hρ (2 * ‖T‖)).comp hB
    change LowerSemicontinuous (fun S : K => ‖(ρ (a S)).val τ.vector - η‖ ^ 2)
    exact (wot_vector_sqDistance_lowerSemicontinuous (H := J) τ.vector η).comp hc
  have hne : (Set.univ : Set K).Nonempty := by
    refine ⟨⟨ofCLM T, hTsa, le_rfl, ?_⟩, Set.mem_univ _⟩
    change T - T ∈ M.commutant
    rw [sub_self]
    exact M.commutant.zero_mem
  have hmid (S : K) (_ : S ∈ Set.univ) (V : K) (_ : V ∈ Set.univ) :
      ∃ Z ∈ (Set.univ : Set K), v Z = (1 / 2 : ℝ) • (v S + v V) := by
    let Z : K := ⟨(1 / 2 : ℝ) • (S.val + V.val),
      boundedSelfAdjointImplementers_midpoint M T S.property V.property⟩
    refine ⟨Z, Set.mem_univ _, ?_⟩
    have he : a Z = (1 / 2 : ℝ) • (a S + a V) := by
      apply Subtype.ext
      change (1 / 2 : ℝ) • (S.val.toCLM + V.val.toCLM) - T =
        (1 / 2 : ℝ) • ((S.val.toCLM - T) + (V.val.toCLM - T))
      module
    change L (a Z) = _
    rw [he, L.map_smul, L.map_add]
  have hbound (S : K) (_ : S ∈ Set.univ) : ‖v S‖ ≤ 2 * ‖T‖ := by
    calc
      ‖v S‖ ≤ ‖ρ (a S)‖ := τ.norm₂_le_norm _
      _ = ‖a S‖ := by
        apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le ρ.toStarAlgHom _)
        have hh := NonUnitalStarAlgHom.norm_apply_le ρ.symm.toStarAlgHom (ρ (a S))
        change ‖ρ.symm (ρ (a S))‖ ≤ ‖ρ (a S)‖ at hh
        rw [ρ.symm_apply_apply] at hh
        exact hh
      _ ≤ 2 * ‖T‖ := han S
  have hfaith : Set.InjOn v Set.univ := by
    intro S _ V _ h
    have he : ρ (a S - a V) = 0 := by
      apply τ.separating
      change (ρ (a S - a V)).val τ.vector = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have ha0 : a S - a V = 0 := by
      have hh := congrArg ρ.symm he
      simpa only [ρ.symm_apply_apply, map_zero] using hh
    have ha : a S = a V := sub_eq_zero.mp ha0
    apply Subtype.ext
    apply toCLM_injective
    have hh := congrArg Subtype.val ha
    change S.val.toCLM - T = V.val.toCLM - T at hh
    have hh' := congrArg (fun x : H →L[ℂ] H => x + T) hh
    simpa only [sub_add_cancel] using hh'
  let F (w : unitary (Algebra M.commutant)) (S : K) : K :=
    ⟨ofCLM (unitaryConj (ambientAlgebraUnitary w) S.val.toCLM),
      boundedSelfAdjointImplementers_conjugate M T hT (ambientAlgebraUnitary w)
        (w : Algebra M.commutant).property S.property⟩
  have honto (w : unitary (Algebra M.commutant)) (S : K) (_ : S ∈ Set.univ) :
      ∃ V ∈ (Set.univ : Set K), F w V = S := by
    refine ⟨F (star w) S, Set.mem_univ _, ?_⟩
    apply Subtype.ext
    apply toCLM_injective
    change unitaryConj (ambientAlgebraUnitary w)
      (unitaryConj (ambientAlgebraUnitary (star w)) S.val.toCLM) = S.val.toCLM
    have he : ambientAlgebraUnitary (star w) = star (ambientAlgebraUnitary w) := by
      apply Subtype.ext
      rfl
    rw [he]
    simpa only [star_star] using
      unitaryConj_star_unitaryConj (star (ambientAlgebraUnitary w)) S.val.toCLM
  have hiso (w : unitary (Algebra M.commutant)) (S : K) (_ : S ∈ Set.univ)
      (V : K) (_ : V ∈ Set.univ) : ‖v (F w S) - v (F w V)‖ = ‖v S - v V‖ := by
    let w' : unitary (Algebra P) := Unitary.map (StarMonoidHom.ofClass ρ.toStarAlgHom) w
    have he : a (F w S) - a (F w V) =
        (w : Algebra M.commutant) * (a S - a V) * star (w : Algebra M.commutant) := by
      apply Subtype.ext
      change unitaryConj (ambientAlgebraUnitary w) S.val.toCLM - T -
        (unitaryConj (ambientAlgebraUnitary w) V.val.toCLM - T) = _
      simp only [sub_sub_sub_cancel_right, ← unitaryConj_sub]
      change (w : Algebra M.commutant).val * (S.val.toCLM - V.val.toCLM) *
        star (w : Algebra M.commutant).val =
        (w : Algebra M.commutant).val * ((S.val.toCLM - T) - (V.val.toCLM - T)) *
        star (w : Algebra M.commutant).val
      rw [sub_sub_sub_cancel_right]
    change ‖L (a (F w S)) - L (a (F w V))‖ = ‖L (a S) - L (a V)‖
    rw [← L.map_sub, he, ← L.map_sub]
    change τ.norm₂ (ρ.toStarAlgHom ((w : Algebra M.commutant) * (a S - a V) *
      star (w : Algebra M.commutant))) = τ.norm₂ (ρ.toStarAlgHom (a S - a V))
    rw [map_mul, map_mul, map_star]
    exact conjugate_norm₂ τ w' (ρ (a S - a V))
  obtain ⟨S, _, hS⟩ := exists_fixed_of_compact_hilbert_image Set.univ isCompact_univ
    hne v hv hmid (2 * ‖T‖) hbound hfaith F (fun _ _ _ => Set.mem_univ _) honto hiso
  have hm : S.val.toCLM ∈ M := by
    apply mem_of_fixed_commutant_unitaries M
    intro w
    exact congrArg (fun Z : K => Z.val.toCLM) (hS w)
  refine ⟨S.val.toCLM, hm, S.property.1, S.property.2.1, ?_⟩
  change T - S.val.toCLM ∈ M.commutant.toSubalgebra
  simpa only [neg_sub] using M.commutant.neg_mem S.property.2.2

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_II1CommutantSpatialSplit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial splitting for every represented type II₁ commutant

The canonical trace representation removes the need for a trace vector
in the original Hilbert space. No separability assumption is used.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_II1_commutant_oai
    (M : VonNeumannAlgebra H) (hN : IsII1Factor M.commutant.toStarSubalgebra)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let hf := traceHilbert_factor hN
  let hu := traceHilbert_nonzero hN
  let P := traceFreeHilbertClosure hf hN.diffuse hN.finite hu
  let e := traceFreeHilbertEquiv hf hN.diffuse hN.finite hu
  let τ : TracialRepresentation P := traceFreeHilbertClosureTrace hf hN.diffuse hN.finite hu
  apply exists_selfAdjoint_split_of_normal_tracial_commutant M P e τ _ T hTsa hT
  intro C
  exact traceFreeHilbertBallMap_continuous hf hN.diffuse hN.finite hu C

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_selfAdjoint_split_of_II1_commutant_oai.{u_1} := @OAI.KadisonKastler.exists_selfAdjoint_split_of_II1_commutant_oai.{u_1}
