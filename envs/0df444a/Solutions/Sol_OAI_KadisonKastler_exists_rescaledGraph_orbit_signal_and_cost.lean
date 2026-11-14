-- Prove2me | solution 1 for OAI.KadisonKastler.exists_rescaledGraph_orbit_signal_and_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:56:44.569236+00:00
-- url     : https://prove2.me/submissions/8b67cea6-4f45-42fa-93e7-fc76564ae9d5

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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K035
import Theorems.Thm_OAI_KadisonKastler_exists_matrixOrbit_graphCost_le_ten

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteMomentSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simultaneous selection from second and fourth moments

This finite probability argument combines the graph-signal second and
fourth moments with a first-moment bound for the clipping cost. All
averages are over the actual nonempty finite probability space.
-/

namespace KadisonKastler

open scoped BigOperators

/-- A fourth-moment signal and a bounded mean cost have a simultaneous
realization. These are the constants used before spectral clipping. -/
theorem exists_signal_and_cost_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (Z B : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (hZ : ∀ i, 0 ≤ Z i) (hB : ∀ i, 0 ≤ B i)
    (hmean : (𝔼 i, Z i) = s)
    (hfourth : (𝔼 i, Z i ^ 2) ≤ 3 * s ^ 2)
    (hcost : (𝔼 i, B i) ≤ 10) :
    ∃ i, s / 2 ≤ Z i ∧ B i ≤ 240 := by
  classical
  by_contra h
  push Not at h
  let χ : ι → ℝ := fun i => if 240 < B i then 1 else 0
  have hχ (i : ι) : 0 ≤ χ i := by dsimp [χ]; split <;> norm_num
  have hχsq (i : ι) : χ i ^ 2 = χ i := by dsimp [χ]; split <;> norm_num
  have hmass : (𝔼 i, χ i) ≤ 1 / 24 := by
    have hi (i : ι) : 240 * χ i ≤ B i := by
      dsimp [χ]
      split_ifs with hb
      · linarith
      · simpa using hB i
    have ht : 240 * (𝔼 i, χ i) ≤ 10 := calc
      _ = (𝔼 i, 240 * χ i) := Finset.mul_expect Finset.univ χ 240
      _ ≤ (𝔼 i, B i) := Finset.expect_le_expect (fun i _ => hi i)
      _ ≤ 10 := hcost
    linarith
  have hsplit (i : ι) : Z i ≤ s / 2 + χ i * Z i := by
    by_cases hb : 240 < B i
    · simp only [χ, hb, ite_true, if_true, one_mul]
      linarith
    · have hz : Z i < s / 2 := lt_of_not_ge (fun hz => hb (h i hz))
      simp only [χ, hb, ite_false, if_false, zero_mul, add_zero]
      exact hz.le
  have hsignal : s / 2 ≤ 𝔼 i, χ i * Z i := by
    have ht : s ≤ s / 2 + (𝔼 i, χ i * Z i) := calc
      _ = (𝔼 i, Z i) := hmean.symm
      _ ≤ (𝔼 i, (s / 2 + χ i * Z i)) := Finset.expect_le_expect (fun i _ => hsplit i)
      _ = s / 2 + (𝔼 i, χ i * Z i) := by rw [Finset.expect_add_distrib]; simp
    linarith
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ χ Z
  simp only [hχsq] at hcs
  have hZsq : 0 ≤ 𝔼 i, Z i ^ 2 := Finset.expect_nonneg (fun i _ => sq_nonneg (Z i))
  have hbound : (𝔼 i, χ i * Z i) ^ 2 ≤ s ^ 2 / 8 := calc
    _ ≤ (𝔼 i, χ i) * (𝔼 i, Z i ^ 2) := hcs
    _ ≤ (1 / 24) * (𝔼 i, Z i ^ 2) := mul_le_mul_of_nonneg_right hmass hZsq
    _ ≤ (1 / 24) * (3 * s ^ 2) := mul_le_mul_of_nonneg_left hfourth (by norm_num)
    _ = s ^ 2 / 8 := by ring
  have hsig0 : 0 ≤ 𝔼 i, χ i * Z i :=
    Finset.expect_nonneg (fun i _ => mul_nonneg (hχ i) (hZ i))
  have hsquare : (s / 2) ^ 2 ≤ (𝔼 i, χ i * Z i) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hsignal 2
  nlinarith [sq_pos_of_pos hs]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteSignFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth moments of finite independent signs

The finite probability space is the set of all Boolean sign assignments.
The four-sign identity and tracial Cauchy–Schwarz give the estimate used
in the bounded-vector test in manuscript §5.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem finiteSign_flip_same (ε : ι → Bool) (i : ι) :
    finiteSign (flipSign i ε) i = -finiteSign ε i := by
  cases h : ε i <;> simp [finiteSign, flipSign, h]

omit [Fintype ι] in
private theorem finiteSign_flip_ne (ε : ι → Bool) {i j : ι} (h : j ≠ i) :
    finiteSign (flipSign i ε) j = finiteSign ε j := by
  simp [finiteSign, flipSign, Function.update_of_ne h]

/-- Coordinate sign orthogonality. -/
theorem finiteSign_pair (i j : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true, if_true, ← pow_two, finiteSign_sq, Fintype.expect_const]
  · rw [ite_eq_right h]
    have he := Fintype.expect_equiv (flipSign i)
      (fun ε => finiteSign ε i * finiteSign ε j)
      (fun ε => -(finiteSign ε i * finiteSign ε j)) (by
        intro ε
        rw [finiteSign_flip_same, finiteSign_flip_ne ε (Ne.symm h)]
        ring)
    rw [Finset.expect_neg_distrib] at he
    linarith

/-- A sign appearing exactly once kills a four-sign expectation. -/
private theorem finiteSign_four_single (i j k l : ι)
    (hij : j ≠ i) (hik : k ≠ i) (hil : l ≠ i) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j *
      finiteSign ε k * finiteSign ε l) = 0 := by
  have he := Fintype.expect_equiv (flipSign i)
    (fun ε => finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l)
    (fun ε => -(finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l)) (by
      intro ε
      rw [finiteSign_flip_same, finiteSign_flip_ne ε hij,
        finiteSign_flip_ne ε hik, finiteSign_flip_ne ε hil]
      ring)
  rw [Finset.expect_neg_distrib] at he
  linarith

/-- The three pairings, with the common diagonal counted only once. -/
theorem finiteSign_four (i j k l : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j *
      finiteSign ε k * finiteSign ε l) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) -
      (if i = j ∧ j = k ∧ k = l then 2 else 0) := by
  by_cases hij : i = j
  · subst j
    have he (ε : ι → Bool) :
        finiteSign ε i * finiteSign ε i * finiteSign ε k * finiteSign ε l =
          finiteSign ε k * finiteSign ε l := by
      rw [← pow_two, finiteSign_sq, one_mul]
    simp_rw [he]
    rw [finiteSign_pair]
    by_cases hik : i = k <;> by_cases hkl : k = l <;>
      simp_all
    all_goals norm_num
  · by_cases hik : i = k
    · subst k
      have he (ε : ι → Bool) :
          finiteSign ε i * finiteSign ε j * finiteSign ε i * finiteSign ε l =
            finiteSign ε j * finiteSign ε l := by
        calc
          _ = finiteSign ε i ^ 2 * (finiteSign ε j * finiteSign ε l) := by ring
          _ = _ := by rw [finiteSign_sq, one_mul]
      simp_rw [he]
      rw [finiteSign_pair]
      simp [hij, Ne.symm hij]
    · by_cases hil : i = l
      · subst l
        have he (ε : ι → Bool) :
            finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε i =
              finiteSign ε j * finiteSign ε k := by
          calc
            _ = finiteSign ε i ^ 2 * (finiteSign ε j * finiteSign ε k) := by ring
            _ = _ := by rw [finiteSign_sq, one_mul]
        simp_rw [he]
        rw [finiteSign_pair]
        simp [hij, hik, Ne.symm hij]
      · rw [finiteSign_four_single i j k l (Ne.symm hij) (Ne.symm hik) (Ne.symm hil)]
        simp [hij, hik, hil]

/-- The fourth-sign identity integrated against any four-index coefficient. -/
theorem expect_finiteSign_four_sum (F : ι → ι → ι → ι → ℝ) :
    (𝔼 ε : ι → Bool, ∑ i, ∑ j, ∑ k, ∑ l,
      (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) * F i j k l) =
      (∑ i, ∑ k, F i i k k) + (∑ i, ∑ j, F i j i j) +
        (∑ i, ∑ j, F i j j i) - 2 * ∑ i, F i i i i := by
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_four,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [ite_and, Finset.mul_sum]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSignMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Hilbert-space second and fourth moments of independent signs

The fourth-moment constant is three. Real Hilbert spaces suffice for the
proof and complex Hilbert spaces are covered by restriction of scalars.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [DecidableEq ι] in
private theorem sign_norm_sq (a : ι → V) (ε : ι → Bool) :
    ‖hilbertSignSum a ε‖ ^ 2 =
      ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) * inner ℝ (a i) (a j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [hilbertSignSum, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [real_inner_comm (a j) (a i)]
    ring

/-- Sign orthogonality gives the exact second moment. -/
theorem expect_hilbertSignSum_sq (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖hilbertSignSum a ε‖ ^ 2) = ∑ i, ‖a i‖ ^ 2 := by
  simp_rw [sign_norm_sq]
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_pair]
  simp

omit [DecidableEq ι] in
private theorem sign_norm_fourth (a : ι → V) (ε : ι → Bool) :
    ‖hilbertSignSum a ε‖ ^ 4 =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) *
          (inner ℝ (a i) (a j) * inner ℝ (a k) (a l)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sign_norm_sq, pow_two, Finset.sum_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Hilbert-space fourth moments require no operator trace. -/
theorem expect_hilbertSignSum_fourth_le (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖hilbertSignSum a ε‖ ^ 4) ≤
      3 * (∑ i, ‖a i‖ ^ 2) ^ 2 := by
  simp_rw [sign_norm_fourth]
  rw [expect_finiteSign_four_sum]
  have hmain : (∑ i, ∑ j, inner ℝ (a i) (a i) * inner ℝ (a j) (a j)) =
      (∑ i, ‖a i‖ ^ 2) ^ 2 := by
    simp only [real_inner_self_eq_norm_sq]
    rw [pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpair : (∑ i, ∑ j, inner ℝ (a i) (a j) * inner ℝ (a i) (a j)) ≤
      (∑ i, ‖a i‖ ^ 2) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (norm_nonneg (inner ℝ (a i) (a j)))
      (norm_inner_le_norm (𝕜 := ℝ) (a i) (a j)) 2
    rw [Real.norm_eq_abs, sq_abs, mul_pow] at h
    simpa only [pow_two] using h
  have hother : (∑ i, ∑ j, inner ℝ (a i) (a j) * inner ℝ (a j) (a i)) =
      ∑ i, ∑ j, inner ℝ (a i) (a j) * inner ℝ (a i) (a j) := by
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [real_inner_comm (a j) (a i)]
  have hdiag : 0 ≤ ∑ i, inner ℝ (a i) (a i) * inner ℝ (a i) (a i) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [hmain, hother]
  linarith

/-- Exact normalized second moment. -/
theorem expect_normalizedHilbertSignSum_sq (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖normalizedHilbertSignSum a ε‖ ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖a i‖ ^ 2 := by
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [normalizedHilbertSignSum, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_expect, hs, expect_hilbertSignSum_sq]

/-- Normalized fourth moment is at most three times the second moment
squared, for every finite family of Hilbert vectors. -/
theorem expect_normalizedHilbertSignSum_fourth_le (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖normalizedHilbertSignSum a ε‖ ^ 4) ≤
      3 * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖a i‖ ^ 2) ^ 2 := by
  have hs : |(Real.sqrt (Fintype.card ι : ℝ))⁻¹| ^ 4 =
      (Fintype.card ι : ℝ)⁻¹ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), inv_pow]
  simp only [normalizedHilbertSignSum, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [← Finset.mul_expect, hs]
  have h := mul_le_mul_of_nonneg_left (expect_hilbertSignSum_fourth_le a)
    (sq_nonneg ((Fintype.card ι : ℝ)⁻¹))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorStateFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nontracial fourth moments of independent signs

The three-pairing sign identity holds for the actual vector functional.
The crossed pairing is bounded after summing the two orders of its
indices. This avoids applying a tracial fourth-moment theorem to the
nontracial vector state in the modular graph argument.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity of the vector functional is a Hilbert norm identity. -/
theorem realVectorState_star_mul_self (Ω : H) (x : H →L[ℂ] H) :
    realVectorState Ω (star x * x) = ‖x Ω‖ ^ 2 := by
  simp only [realVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphSignalSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simultaneous graph signal and clipping-cost selection

The normalized sign sum is passed through an actual real-linear signal
map. A constant orbit signal gives its exact second moment and the
Hilbert fourth-moment bound. Finite selection then retains the signal
and bounds the actual vector-state clipping cost in the same sample.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {I G : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype G] [Nonempty G]

omit [DecidableEq I] [Nonempty I] in
/-- A real-linear signal map commutes with the normalized sign sum. -/
theorem map_normalizedFiniteSignSum (L : (H →L[ℂ] H) →ₗ[ℝ] V)
    (a : I → H →L[ℂ] H) (ε : I → Bool) :
    L (normalizedFiniteSignSum a ε) = normalizedHilbertSignSum (fun i => L (a i)) ε := by
  simp only [normalizedFiniteSignSum, normalizedHilbertSignSum, finiteSignSum,
    hilbertSignSum, map_smul, map_sum]

/-- All sampled summands have the same signal variance. -/
theorem sampled_sign_signal_second (L : (H →L[ℂ] H) →ₗ[ℝ] V)
    (a : G → H →L[ℂ] H) (s : ℝ) (hsignal : ∀ g, ‖L (a g)‖ ^ 2 = s) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 2) = s := by
  simp_rw [map_normalizedFiniteSignSum, expect_normalizedHilbertSignSum_sq]
  simp only [hsignal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hm : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [← mul_assoc, inv_mul_cancel₀ hm, one_mul, Fintype.expect_const]

/-- The signal fourth moment is controlled independently of the number
of matrix samples. -/
theorem sampled_sign_signal_fourth (L : (H →L[ℂ] H) →ₗ[ℝ] V)
    (a : G → H →L[ℂ] H) (s : ℝ) (hsignal : ∀ g, ‖L (a g)‖ ^ 2 = s) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 4) ≤ 3 * s ^ 2 := by
  have hm : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hω (ω : I → G) :
      (𝔼 ε : I → Bool,
        ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 4) ≤ 3 * s ^ 2 := by
    simp only [map_normalizedFiniteSignSum]
    have h := expect_normalizedHilbertSignSum_fourth_le (fun i => L (a (ω i)))
    simpa only [hsignal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hm, one_mul] using h
  calc
    _ ≤ (𝔼 _ω : I → G, 3 * s ^ 2) := Finset.expect_le_expect (fun ω _ => hω ω)
    _ = _ := Fintype.expect_const _

/-- The clipping cost is nonnegative for a nonnegative graph scale. -/
theorem graphMomentCost_nonneg (Ω : H) {k : ℝ} (hk : 0 ≤ k) (x : H →L[ℂ] H) :
    0 ≤ graphMomentCost Ω k x := by
  have hright : realVectorState Ω ((star x * x) ^ 2) = ‖(star x * x) Ω‖ ^ 2 := by
    simpa only [pow_two, star_mul, star_star] using
      realVectorState_star_mul_self Ω (star x * x)
  have hleft : realVectorState Ω ((x * star x) ^ 2) = ‖(x * star x) Ω‖ ^ 2 := by
    simpa only [pow_two, star_mul, star_star] using
      realVectorState_star_mul_self Ω (x * star x)
  have hsecond : realVectorState Ω (x * star x) = ‖star x Ω‖ ^ 2 := by
    simpa only [star_star] using realVectorState_star_mul_self Ω (star x)
  simp only [graphMomentCost, realVectorState_star_mul_self, hright, hleft, hsecond]
  positivity

/-- One actual finite sample simultaneously retains half of the signal
variance and has clipping cost at most 240. -/
theorem exists_sampled_sign_signal_and_cost
    (Ω : H) {k : ℝ} (hk : 0 ≤ k)
    (L : (H →L[ℂ] H) →ₗ[ℝ] V) (a : G → H →L[ℂ] H)
    {s : ℝ} (hs : 0 < s) (hsignal : ∀ g, ‖L (a g)‖ ^ 2 = s)
    (hcost : (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε)) ≤ 10) :
    ∃ ω : I → G, ∃ ε : I → Bool,
      s / 2 ≤ ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 2 ∧
      graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε) ≤ 240 := by
  let Z : (I → G) × (I → Bool) → ℝ := fun p =>
    ‖L (normalizedFiniteSignSum (fun i => a (p.1 i)) p.2)‖ ^ 2
  let B : (I → G) × (I → Bool) → ℝ := fun p =>
    graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (p.1 i)) p.2)
  have hmean : (𝔼 p, Z p) = s := by
    rw [show (𝔼 p, Z p) = 𝔼 ω : I → G, 𝔼 ε : I → Bool, Z (ω, ε) from
      by simpa only [Finset.univ_product_univ] using
        Finset.expect_product (Finset.univ : Finset (I → G))
          (Finset.univ : Finset (I → Bool)) Z]
    exact sampled_sign_signal_second L a s hsignal
  have hfourth : (𝔼 p, Z p ^ 2) ≤ 3 * s ^ 2 := by
    rw [show (𝔼 p, Z p ^ 2) = 𝔼 ω : I → G, 𝔼 ε : I → Bool, Z (ω, ε) ^ 2 from
      by simpa only [Finset.univ_product_univ] using
        Finset.expect_product (Finset.univ : Finset (I → G))
          (Finset.univ : Finset (I → Bool)) (fun p => Z p ^ 2)]
    simpa only [Z, ← pow_mul] using sampled_sign_signal_fourth L a s hsignal
  have hB : (𝔼 p, B p) ≤ 10 := by
    rw [show (𝔼 p, B p) = 𝔼 ω : I → G, 𝔼 ε : I → Bool, B (ω, ε) from
      by simpa only [Finset.univ_product_univ] using
        Finset.expect_product (Finset.univ : Finset (I → G))
          (Finset.univ : Finset (I → Bool)) B]
    exact hcost
  obtain ⟨p, hp⟩ := exists_signal_and_cost_le Z B hs
    (fun _ => sq_nonneg _) (fun _ => graphMomentCost_nonneg Ω hk _) hmean hfourth hB
  exact ⟨p.1, p.2, hp⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledGraphAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common unitary action on rescaled graphs

Left and right multiplication by common unitaries acts on graph vectors
through one unitary of the fixed two-coordinate Hilbert space. Thus each
closed graph reduces this unitary whenever the right action belongs to
the relevant commutant and has the prescribed value on the common vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem right_operator_on_algebra_vector
    (P : VonNeumannAlgebra H) (Ω : H) (a b : H →L[ℂ] H)
    (ha : a ∈ P.commutant) (x : Algebra P) (hΩ : a Ω = b Ω) :
    a (x.val Ω) = x.val (b Ω) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp ha x.val x.property
  calc
    a (x.val Ω) = x.val (a Ω) :=
      (congrArg (fun T : H →L[ℂ] H => T Ω) hc).symm
    _ = x.val (b Ω) := by rw [hΩ]

/-- Exact action on graph vectors, before any closure argument. -/
theorem rescaledGraphAction_vector
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (r s : unitary (H →L[ℂ] H))
    (hsright : conjugationOperator J (star (s : H →L[ℂ] H)) ∈ P.commutant)
    (hrright : conjugationOperator J (r : H →L[ℂ] H) ∈ P.commutant)
    (hsΩ : conjugationOperator J (star (s : H →L[ℂ] H)) Ω = (s : H →L[ℂ] H) Ω)
    (hrΩ : conjugationOperator J (r : H →L[ℂ] H) Ω = star (r : H →L[ℂ] H) Ω)
    (x : Algebra P) :
    (rescaledGraphAction J hJ r s :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x.val) =
        rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 0 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 0
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_zero,
      rescaledGraphVector_zero, Submonoid.coe_mul, mul_apply_eq_comp,
      conjugationUnitary_coe, Unitary.coe_star]
    rw [right_operator_on_algebra_vector P Ω _ _ hsright x hsΩ]
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 1 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 1
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_one,
      rescaledGraphVector_one, conjugationUnitary_coe]
    rw [LinearMapClass.map_smul_of_tower]
    congr 1
    change J (star (s : H →L[ℂ] H)
      (conjugationOperator J (r : H →L[ℂ] H) (J (J (star x.val Ω))))) =
        J (star ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) Ω)
    rw [hJ]
    have hc := right_operator_on_algebra_vector P Ω _ _ hrright (star x) hrΩ
    change conjugationOperator J (r : H →L[ℂ] H) (star x.val Ω) =
      star x.val (star (r : H →L[ℂ] H) Ω) at hc
    rw [hc]
    simp only [star_mul, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphOrbitSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual orbit samples retaining the rescaled graph signal

The finite matrix moment estimate and the Hilbert sign selection are
combined here. The signal is the image of the graph vector under the
specified bounded operator; its invariance is derived from the common
unitary graph action.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Commutation with the unitary graph action preserves the signal on
an actual two-sided orbit. -/
theorem norm_graphSignal_unitaryDoubleOrbit
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (u v : unitary (H →L[ℂ] H))
    (hvright : conjugationOperator J (v : H →L[ℂ] H) ∈ M.commutant)
    (huright : conjugationOperator J (u : H →L[ℂ] H) ∈ M.commutant)
    (hvΩ : conjugationOperator J (v : H →L[ℂ] H) Ω = star (v : H →L[ℂ] H) Ω)
    (huΩ : conjugationOperator J (u : H →L[ℂ] H) Ω = star (u : H →L[ℂ] H) Ω)
    (hT : T * (rescaledGraphAction J hJ u (star v) :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ u (star v) :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T)
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    ‖T (rescaledGraphVector J Ω c (unitaryDoubleOrbit x u v))‖ =
      ‖T (rescaledGraphVector J Ω c x)‖ := by
  have hf := rescaledGraphAction_vector M J hJ Ω c u (star v)
    (by simpa only [Unitary.coe_star, star_star] using hvright) huright
    (by simpa only [Unitary.coe_star, star_star] using hvΩ) huΩ ⟨x, hx⟩
  change (rescaledGraphAction J hJ u (star v) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x) =
    rescaledGraphVector J Ω c (unitaryDoubleOrbit x u v) at hf
  rw [← hf]
  have he := congrArg (fun A : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H =>
    A (rescaledGraphVector J Ω c x)) hT
  simp only [mul_apply_eq_comp] at he
  rw [he, Unitary.norm_map]

section Selection

variable (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M)

include M hΩ hmono hEM hirr hc hx

/-- The matrix cost construction and a constant orbit signal select one
actual sampled operator, rather than a separate sample for each bound. -/
theorem exists_matrixOrbit_signal_and_cost
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k : ℝ} (hk : 1 ≤ k) (hxnorm : ‖x Ω‖ ^ 2 + k * ‖star x Ω‖ ^ 2 = 1)
    (L : (H →L[ℂ] H) →ₗ[ℝ] V) {s : ℝ} (hs : 0 < s)
    (hsignal : ∀ j g, ‖L (matrixOrbitSample (E j) x g)‖ ^ 2 = s) :
    ∃ j m, ∃ ω : Fin m → MatrixOrbitIndex (d j), ∃ ε : Fin m → Bool,
      1 ≤ m ∧
      s / 2 ≤ ‖L (normalizedFiniteSignSum
        (fun i => matrixOrbitSample (E j) x (ω i)) ε)‖ ^ 2 ∧
      graphMomentCost Ω k (normalizedFiniteSignSum
        (fun i => matrixOrbitSample (E j) x (ω i)) ε) ≤ 240 := by
  obtain ⟨j, m, hm, hcost⟩ := exists_matrixOrbit_graphCost_le_ten M Ω hΩ d E hmono hEM
    hirr hc x hx hk hxnorm
  let : NeZero m := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)⟩
  obtain ⟨ω, ε, hsignal', hcost'⟩ := exists_sampled_sign_signal_and_cost (I := Fin m)
    Ω (le_trans zero_le_one hk) L (matrixOrbitSample (E j) x) hs (hsignal j) hcost
  exact ⟨j, m, ω, ε, hm, hsignal', hcost'⟩

/-- The genuine common graph action discharges the signal-invariance
premise in the simultaneous selection theorem. -/
theorem exists_rescaledGraph_orbit_signal_and_cost_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {k : ℝ} (hk : 1 ≤ k) (hxnorm : ‖x Ω‖ ^ 2 + k * ‖star x Ω‖ ^ 2 = 1)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (hs : 0 < ‖T (rescaledGraphVector J Ω (Real.sqrt k) x)‖)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hT : ∀ j (u v : unitary (H →L[ℂ] H)), (u : H →L[ℂ] H) ∈ (E j).algebra →
      (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ j m, ∃ ω : Fin m → MatrixOrbitIndex (d j), ∃ ε : Fin m → Bool,
      1 ≤ m ∧
      ‖T (rescaledGraphVector J Ω (Real.sqrt k) x)‖ ^ 2 / 2 ≤
        ‖T (rescaledGraphVector J Ω (Real.sqrt k)
          (normalizedFiniteSignSum (fun i => matrixOrbitSample (E j) x (ω i)) ε))‖ ^ 2 ∧
      graphMomentCost Ω k (normalizedFiniteSignSum
        (fun i => matrixOrbitSample (E j) x (ω i)) ε) ≤ 240 := by
  let : InnerProductSpace ℝ (TomitaGraphHilbert H) := InnerProductSpace.complexToReal
  apply exists_matrixOrbit_signal_and_cost M Ω hΩ d E hmono hEM hirr hc x hx hk hxnorm
    (rescaledGraphSignalMap J Ω (Real.sqrt k) T) (sq_pos_of_pos hs)
  intro j g
  let u := matrixUnitSignedRepresentation (E j) g.1
  let v := matrixUnitSignedRepresentation (E j) g.2
  have hu : (u : H →L[ℂ] H) ∈ (E j).algebra := matrixUnitSignedRepresentation_mem _ _
  have hv : (v : H →L[ℂ] H) ∈ (E j).algebra := matrixUnitSignedRepresentation_mem _ _
  have hvs := (E j).algebra.star_mem' hv
  have hus := (E j).algebra.star_mem' hu
  have he := norm_graphSignal_unitaryDoubleOrbit M J hJ Ω (Real.sqrt k) T u v
    (by simpa only [star_star] using hcomm j _ hvs)
    (by simpa only [star_star] using hcomm j _ hus)
    (by simpa only [star_star] using hvector j _ hvs)
    (by simpa only [star_star] using hvector j _ hus)
    (hT j u (star v) hu (by
      change star (v : H →L[ℂ] H) ∈ (E j).algebra.carrier
      exact hvs)) x hx
  simp only [rescaledGraphSignalMap_apply, matrixOrbitSample, u, v, he]

end Selection

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_rescaledGraph_orbit_signal_and_cost_oai.{u_1} := @OAI.KadisonKastler.exists_rescaledGraph_orbit_signal_and_cost_oai.{u_1}
