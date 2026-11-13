-- Prove2me | solution 1 for OAI.KadisonKastler.exists_matrixOrbit_graphCost_le_ten
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:16:19.06282+00:00
-- url     : https://prove2.me/submissions/15cb28a0-bd05-43e5-aefc-acd6f6391b20

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Definitions.Def_Q260K020
import Theorems.Thm_OAI_KadisonKastler_matrixOrbit_graphPairing_tendsto

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteIndependentSamples
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coordinate independence in finite product samples

Uniformly sampling a finite function is the concrete probability space
used for the independent left and right matrix unitaries. One- and
two-coordinate expectations reduce to their actual finite averages.
-/

namespace KadisonKastler

open scoped BigOperators

section

variable {I G X : Type*} [Fintype I] [DecidableEq I]
  [Fintype G] [Nonempty G] [AddCommMonoid X] [Module ℚ≥0 X]

/-- One coordinate of a uniformly sampled function has the uniform law. -/
theorem expect_sample_coordinate (i : I) (f : G → X) :
    (𝔼 ω : I → G, f (ω i)) = 𝔼 g : G, f g := by
  have he := Fintype.expect_equiv (Equiv.funSplitAt i G)
    (fun ω : I → G => f (ω i))
    (fun p : G × ({j : I // j ≠ i} → G) => f p.1) (fun _ => rfl)
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset G)
    (Finset.univ : Finset ({j : I // j ≠ i} → G))
    (fun p : G × ({j : I // j ≠ i} → G) => f p.1)
  simpa only [Finset.univ_product_univ, Fintype.expect_const] using hp

/-- Distinct coordinates in the finite product are independent. -/
theorem expect_sample_two_coordinates {i j : I} (hij : i ≠ j) (f : G → G → X) :
    (𝔼 ω : I → G, f (ω i) (ω j)) = 𝔼 g : G, 𝔼 h : G, f g h := by
  have he := Fintype.expect_equiv (Equiv.funSplitAt i G)
    (fun ω : I → G => f (ω i) (ω j))
    (fun p : G × ({k : I // k ≠ i} → G) => f p.1 (p.2 ⟨j, Ne.symm hij⟩))
    (fun _ => rfl)
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset G)
    (Finset.univ : Finset ({k : I // k ≠ i} → G))
    (fun p : G × ({k : I // k ≠ i} → G) => f p.1 (p.2 ⟨j, Ne.symm hij⟩))
  rw [show (𝔼 p : G × ({k : I // k ≠ i} → G), f p.1 (p.2 ⟨j, Ne.symm hij⟩)) =
      𝔼 g : G, 𝔼 ω : ({k : I // k ≠ i} → G), f g (ω ⟨j, Ne.symm hij⟩) from
    by simpa only [Finset.univ_product_univ] using hp]
  simp_rw [expect_sample_coordinate]

end

section

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

/-- Summing the two-coordinate law separates the diagonal samples from
the independent off-diagonal samples, with their exact multiplicities. -/
theorem expect_sample_pair_sum (f : G → G → ℝ) :
    (𝔼 ω : I → G, ∑ i, ∑ j, f (ω i) (ω j)) =
      (Fintype.card I : ℝ) * (𝔼 g : G, f g g) +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) *
          (𝔼 g : G, 𝔼 h : G, f g h) := by
  simp only [Finset.expect_sum_comm]
  let d : ℝ := 𝔼 g : G, f g g
  let c : ℝ := 𝔼 g : G, 𝔼 h : G, f g h
  have hp (i j : I) : (𝔼 ω : I → G, f (ω i) (ω j)) =
      if i = j then d else c := by
    by_cases h : i = j
    · subst j
      simpa only [ite_true, if_true, d] using expect_sample_coordinate (G := G) i (fun g => f g g)
    · simpa only [h, ite_false, if_false, c] using expect_sample_two_coordinates h f
  simp_rw [hp]
  have hi (i j : I) : (if i = j then d else c) = c + (if i = j then d - c else 0) := by
    split_ifs <;> ring
  simp_rw [hi, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) * c) +
    (Fintype.card I : ℝ) * (d - c) = _
  dsimp only [d, c]
  ring

end

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Exact normalized second moment. -/
theorem expect_normalizedHilbertSignSum_sq (a : ι → V) :
    (𝔼 ε : ι → Bool, ‖normalizedHilbertSignSum a ε‖ ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖a i‖ ^ 2 := by
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [normalizedHilbertSignSum, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_expect, hs, expect_hilbertSignSum_sq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStateMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Mixed vector-state moments of finite matrix orbits

These are the two independent-copy pairings used in graph flattening.
The finite signed-permutation averages are actual matrix averages, and
only the common vector-state centralizer identity is used. In particular
none of the state calculations presupposes a tracial ambient state.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The crossed fourth-moment pairing is controlled by the two positive
pairings. This is the vector-state version, with no trace assumption. -/
theorem operatorVectorState_square_re_le (Ω : H) (a : H →L[ℂ] H) :
    2 * (operatorVectorState Ω (a ^ 2)).re ≤
      ‖a Ω‖ ^ 2 + ‖(star a) Ω‖ ^ 2 := by
  have hn := sq_nonneg ‖(star a) Ω - a Ω‖
  rw [norm_sub_sq (𝕜 := ℂ)] at hn
  have he : inner ℂ ((star a) Ω) (a Ω) = operatorVectorState Ω (a ^ 2) := by
    simp only [operatorVectorState_apply, pow_two, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [he] at hn
  change 0 ≤ ‖(star a) Ω‖ ^ 2 -
    2 * (operatorVectorState Ω (a ^ 2)).re + ‖a Ω‖ ^ 2 at hn
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorStateFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [DecidableEq ι] in
private theorem sign_fourth_integrand (Ω : H)
    (a : ι → H →L[ℂ] H) (ε : ι → Bool) :
    realVectorState Ω ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) *
          realVectorState Ω ((star (a i) * a j) * (star (a k) * a l)) := by
  have hprod : star (finiteSignSum a ε) * finiteSignSum a ε =
      ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) • (star (a i) * a j) := by
    simp only [finiteSignSum, star_sum, star_smul, star_trivial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_comm (finiteSign ε j) (finiteSign ε i)]
  rw [hprod, pow_two, Finset.sum_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Exact three-pairing expansion in an arbitrary vector state. The
third pairing stays in its original order; no trace cycling is used. -/
theorem expect_finiteSignSum_vector_fourth (Ω : H) (a : ι → H →L[ℂ] H) :
    (𝔼 ε : ι → Bool,
      realVectorState Ω ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) =
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a i) * (star (a j) * a j))) +
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) ^ 2)) +
      (∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) * (star (a j) * a i))) -
      2 * ∑ i, realVectorState Ω ((star (a i) * a i) ^ 2) := by
  simp_rw [sign_fourth_integrand]
  simpa only [pow_two] using expect_finiteSign_four_sum
    (fun i j k l => realVectorState Ω ((star (a i) * a j) * (star (a k) * a l)))

omit [DecidableEq ι] in
/-- Summing both index orders bounds the crossed pairing by the positive
pairing, even though the state is not tracial. -/
theorem sum_vectorState_crossed_le (Ω : H) (a : ι → H →L[ℂ] H) :
    (∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) ^ 2)) ≤
      ∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) * (star (a j) * a i)) := by
  have hp (i j : ι) :
      2 * realVectorState Ω ((star (a i) * a j) ^ 2) ≤
        realVectorState Ω ((star (a j) * a i) * (star (a i) * a j)) +
        realVectorState Ω ((star (a i) * a j) * (star (a j) * a i)) := by
    have h := operatorVectorState_square_re_le Ω (star (a i) * a j)
    have h₁ := realVectorState_star_mul_self Ω (star (a i) * a j)
    have h₂ := realVectorState_star_mul_self Ω (star (a j) * a i)
    simp only [star_mul, star_star] at h₁ h₂ h
    change 2 * realVectorState Ω ((star (a i) * a j) ^ 2) ≤ _ at h
    rw [← h₁, ← h₂] at h
    exact h
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hp i j))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have hswap :
      (∑ i, ∑ j, realVectorState Ω ((star (a j) * a i) * (star (a i) * a j))) =
      ∑ i, ∑ j, realVectorState Ω ((star (a i) * a j) * (star (a j) * a i)) :=
    Finset.sum_comm
  rw [hswap] at hs
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IndependentOrbitMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth moments for independently sampled operator coefficients

The diagonal correction in the sign expansion is retained before the
independent samples are averaged. Consequently its coefficient is
`1/m`, while the two off-diagonal pairings have coefficient `1-1/m`.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H I G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

/-- Exact diagonal counting and the crossed-pairing inequality give the
unnormalized sampled fourth-moment estimate. -/
theorem expect_sampledSignSum_vector_fourth_le
    (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω ((star (finiteSignSum (fun i => a (ω i)) ε) *
        finiteSignSum (fun i => a (ω i)) ε) ^ 2)) ≤
      (Fintype.card I : ℝ) * (𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)) +
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) *
        ((𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))) +
          2 * (𝔼 g, 𝔼 h, realVectorState Ω
            ((star (a g) * a h) * (star (a h) * a g)))) := by
  let D : ℝ := 𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)
  let P : ℝ := 𝔼 g, 𝔼 h,
    realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))
  let Q : ℝ := 𝔼 g, 𝔼 h,
    realVectorState Ω ((star (a g) * a h) * (star (a h) * a g))
  have hpoint (ω : I → G) :
      (𝔼 ε : I → Bool,
        realVectorState Ω ((star (finiteSignSum (fun i => a (ω i)) ε) *
          finiteSignSum (fun i => a (ω i)) ε) ^ 2)) ≤
      (∑ i, ∑ j, realVectorState Ω
        ((star (a (ω i)) * a (ω i)) * (star (a (ω j)) * a (ω j)))) +
      2 * (∑ i, ∑ j, realVectorState Ω
        ((star (a (ω i)) * a (ω j)) * (star (a (ω j)) * a (ω i)))) -
      2 * ∑ i, realVectorState Ω ((star (a (ω i)) * a (ω i)) ^ 2) := by
    rw [expect_finiteSignSum_vector_fourth]
    have hc := sum_vectorState_crossed_le Ω (fun i => a (ω i))
    linarith
  have hP : (𝔼 ω : I → G, ∑ i, ∑ j, realVectorState Ω
      ((star (a (ω i)) * a (ω i)) * (star (a (ω j)) * a (ω j)))) =
      (Fintype.card I : ℝ) * D +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * P := by
    simpa only [D, P, pow_two] using expect_sample_pair_sum (I := I)
      (fun g h => realVectorState Ω ((star (a g) * a g) * (star (a h) * a h)))
  have hQ : (𝔼 ω : I → G, ∑ i, ∑ j, realVectorState Ω
      ((star (a (ω i)) * a (ω j)) * (star (a (ω j)) * a (ω i)))) =
      (Fintype.card I : ℝ) * D +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * Q := by
    simpa only [D, Q, pow_two] using expect_sample_pair_sum (I := I)
      (fun g h => realVectorState Ω ((star (a g) * a h) * (star (a h) * a g)))
  have hD : (𝔼 ω : I → G, ∑ i,
      realVectorState Ω ((star (a (ω i)) * a (ω i)) ^ 2)) =
      (Fintype.card I : ℝ) * D := by
    rw [Finset.expect_sum_comm]
    have hi (i : I) : (𝔼 ω : I → G,
        realVectorState Ω ((star (a (ω i)) * a (ω i)) ^ 2)) = D :=
      expect_sample_coordinate i (fun g => realVectorState Ω ((star (a g) * a g) ^ 2))
    simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun ω _ => hpoint ω)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, hP, hQ, hD] at havg
  change _ ≤ (Fintype.card I : ℝ) * D +
    (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * (P + 2 * Q)
  linarith

omit [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G] in
private theorem vector_fourth_smul (Ω : H) (t : ℝ) (x : H →L[ℂ] H) :
    realVectorState Ω ((star (t • x) * (t • x)) ^ 2) =
      t ^ 4 * realVectorState Ω ((star x * x) ^ 2) := by
  simp only [pow_two, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, map_smul, smul_eq_mul]
  ring

variable [Nonempty I]

/-- Normalizing by the sample size yields the exact `1/m` diagonal cost
and the two independent off-diagonal moments. -/
theorem expect_sampledNormalizedSignSum_vector_fourth_le
    (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω ((star (normalizedFiniteSignSum (fun i => a (ω i)) ε) *
        normalizedFiniteSignSum (fun i => a (ω i)) ε) ^ 2)) ≤
      (𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)) / Fintype.card I +
      (1 - (Fintype.card I : ℝ)⁻¹) *
        ((𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))) +
          2 * (𝔼 g, 𝔼 h, realVectorState Ω
            ((star (a g) * a h) * (star (a h) * a g)))) := by
  have hs : (Real.sqrt (Fintype.card I : ℝ))⁻¹ ^ 4 =
      (Fintype.card I : ℝ)⁻¹ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), inv_pow]
  simp only [normalizedFiniteSignSum, vector_fourth_smul]
  simp_rw [← Finset.mul_expect]
  rw [hs]
  refine (mul_le_mul_of_nonneg_left (expect_sampledSignSum_vector_fourth_le (I := I) Ω a)
    (sq_nonneg ((Fintype.card I : ℝ)⁻¹))).trans_eq ?_
  have hm : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth-moment pairings of actual two-sided matrix orbits

The sampled elements are `u*x*v*`. Their first and third sign-pairing
terms reduce exactly to the independent matrix averages in
`MatrixStateMoments`; the reductions use the vector-state centralizer,
not a trace identity for arbitrary elements.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The left orbit unitary cancels from the right square. -/
theorem unitaryDoubleOrbit_star_mul_self (x : H →L[ℂ] H)
    (u v : unitary (H →L[ℂ] H)) :
    star (unitaryDoubleOrbit x u v) * unitaryDoubleOrbit x u v =
      unitaryConj v (star x * x) := by
  simp only [unitaryDoubleOrbit, star_mul, star_star, unitaryConj]
  calc
    _ = (v : H →L[ℂ] H) * star x *
        (star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) * x * star (v : H →L[ℂ] H) := by
      noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem u.property]; noncomm_ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitSampleLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite laws of the actual matrix-orbit samples

This converts the complex four-variable matrix-average identities to
real moment identities for a single product-valued sample. It supplies
the diagonal and the two off-diagonal inputs to the independent-sample
fourth-moment estimate.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem state_conj_p1 (M : VonNeumannAlgebra H) (Ω : H)
    (v : unitary (H →L[ℂ] H)) (hv : (v : H →L[ℂ] H) ∈ M)
    (hc : ∀ z ∈ M, inner ℂ Ω (((v : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (v : H →L[ℂ] H)) Ω))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    realVectorState Ω (unitaryConj v a) = realVectorState Ω a := by
  have h := hc (a * star (v : H →L[ℂ] H))
    (M.mul_mem ha (M.toStarSubalgebra.star_mem' hv))
  apply congrArg Complex.re
  change inner ℂ Ω (((v : H →L[ℂ] H) * a * star (v : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (a Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem v.property, mul_one] using h

/-- The fourth moment of a single orbit sample is unchanged by its two
unitaries, since the right unitary belongs to the state's centralizer. -/
theorem matrixOrbit_diagonal_fourth
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (g : MatrixOrbitIndex d) :
    realVectorState Ω ((star (matrixOrbitSample E x g) * matrixOrbitSample E x g) ^ 2) =
      realVectorState Ω ((star x * x) ^ 2) := by
  change realVectorState Ω ((star (unitaryDoubleOrbit x _ _) *
    unitaryDoubleOrbit x _ _) ^ 2) = _
  rw [unitaryDoubleOrbit_star_mul_self]
  have he := (map_pow (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H)
    (matrixUnitSignedRepresentation E g.2)) (star x * x) 2).symm
  change (unitaryConj (matrixUnitSignedRepresentation E g.2) (star x * x)) ^ 2 =
    unitaryConj (matrixUnitSignedRepresentation E g.2) ((star x * x) ^ 2) at he
  rw [he]
  exact state_conj_p1 M Ω _ (hEM (matrixUnitSignedRepresentation_mem E g.2))
    (hc _ (matrixUnitSignedRepresentation_mem E g.2)) _
    (M.pow_mem (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx) 2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphMomentBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Expected costs before graph clipping

The cost uses the actual vector state and the two fourth powers. The
finite-sample estimate retains the diagonal correction, so increasing
the number of samples removes the diagonal cost. The final scalar lemma
chooses a stage and a sample size from convergence of the mixed moments.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

attribute [local instance] OAI.KadisonKastler.graphMomentRealInner
omit [DecidableEq I] in
/-- Applying an operator sign sum to a vector is the Hilbert sign sum. -/
theorem normalizedFiniteSignSum_apply (a : I → H →L[ℂ] H) (ε : I → Bool) (Ω : H) :
    (normalizedFiniteSignSum a ε) Ω =
      normalizedHilbertSignSum (fun i => a i Ω) ε := by
  simp only [normalizedFiniteSignSum, normalizedHilbertSignSum, finiteSignSum,
    hilbertSignSum, smul_apply, sum_apply]

/-- The exact second moment holds for the vector state, without traciality. -/
theorem expect_normalizedSignSum_vector_second (Ω : H) (a : I → H →L[ℂ] H) :
    (𝔼 ε : I → Bool,
      realVectorState Ω (star (normalizedFiniteSignSum a ε) * normalizedFiniteSignSum a ε)) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, realVectorState Ω (star (a i) * a i) := by
  simp only [realVectorState_star_mul_self, normalizedFiniteSignSum_apply]
  exact expect_normalizedHilbertSignSum_sq (fun i => a i Ω)

omit [DecidableEq I] in
private theorem star_normalizedSignSum (a : I → H →L[ℂ] H) (ε : I → Bool) :
    star (normalizedFiniteSignSum a ε) = normalizedFiniteSignSum (fun i => star (a i)) ε := by
  simp only [normalizedFiniteSignSum, finiteSignSum, star_smul, star_trivial, star_sum]

/-- The second moment after independent sampling is the single-sample
second moment. -/
theorem expect_sampledNormalizedSignSum_vector_second
    [Nonempty I] (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω (star (normalizedFiniteSignSum (fun i => a (ω i)) ε) *
        normalizedFiniteSignSum (fun i => a (ω i)) ε)) =
      𝔼 g, realVectorState Ω (star (a g) * a g) := by
  simp_rw [expect_normalizedSignSum_vector_second]
  rw [← Finset.mul_expect, Finset.expect_sum_comm]
  have hi (i : I) : (𝔼 ω : I → G, realVectorState Ω (star (a (ω i)) * a (ω i))) =
      𝔼 g, realVectorState Ω (star (a g) * a g) :=
    expect_sample_coordinate i (fun g => realVectorState Ω (star (a g) * a g))
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- The left square has the corresponding exact second moment. -/
theorem expect_sampledNormalizedSignSum_vector_left_second
    [Nonempty I] (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω (normalizedFiniteSignSum (fun i => a (ω i)) ε *
        star (normalizedFiniteSignSum (fun i => a (ω i)) ε))) =
      𝔼 g, realVectorState Ω (a g * star (a g)) := by
  simpa only [star_normalizedSignSum, star_star] using
    expect_sampledNormalizedSignSum_vector_second (I := I) Ω (fun g => star (a g))

/-- The actual cost of independently sampled normalized sign sums is
bounded by its single-sample, diagonal, and off-diagonal moments. -/
theorem expect_sampled_graphMomentCost_le [Nonempty I]
    (Ω : H) {k : ℝ} (hk : 0 ≤ k) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε)) ≤
      orbitSecondMoment Ω k a +
      (orbitDiagonalMoment Ω a + k * orbitDiagonalMoment Ω (fun g => star (a g))) /
        Fintype.card I +
      (1 - (Fintype.card I : ℝ)⁻¹) *
        (orbitFirstPairMoment Ω a + 2 * orbitThirdPairMoment Ω a +
          k * (orbitFirstPairMoment Ω (fun g => star (a g)) +
            2 * orbitThirdPairMoment Ω (fun g => star (a g)))) := by
  have hr := expect_sampledNormalizedSignSum_vector_fourth_le (I := I) Ω a
  have hl := expect_sampledNormalizedSignSum_vector_fourth_le (I := I) Ω (fun g => star (a g))
  simp_rw [← star_normalizedSignSum, star_star] at hl
  have hcost :
      (𝔼 ω : I → G, 𝔼 ε : I → Bool,
        graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε)) =
      orbitSecondMoment Ω k a +
      (𝔼 ω : I → G, 𝔼 ε : I → Bool,
        realVectorState Ω ((star (normalizedFiniteSignSum (fun i => a (ω i)) ε) *
          normalizedFiniteSignSum (fun i => a (ω i)) ε) ^ 2)) +
      k * (𝔼 ω : I → G, 𝔼 ε : I → Bool,
        realVectorState Ω ((normalizedFiniteSignSum (fun i => a (ω i)) ε *
          star (normalizedFiniteSignSum (fun i => a (ω i)) ε)) ^ 2)) := by
    simp only [graphMomentCost, Finset.expect_add_distrib, ← Finset.mul_expect,
      expect_sampledNormalizedSignSum_vector_second,
      expect_sampledNormalizedSignSum_vector_left_second, orbitSecondMoment]
  rw [hcost]
  have hkl := mul_le_mul_of_nonneg_left hl hk
  have hb := add_le_add_left (add_le_add hr hkl) (orbitSecondMoment Ω k a)
  convert hb using 1 <;>
    (try simp only [orbitDiagonalMoment, orbitFirstPairMoment, orbitThirdPairMoment, star_star]) <;> first | rfl | ring

/-- The scalar off-diagonal cost stays bounded uniformly in the graph
rescaling when `α + k β = 1` and `k ≥ 1`. -/
theorem graph_pairing_scalar_le_six {α β k : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hk : 1 ≤ k) (hn : α + k * β ≤ 1) :
    α ^ 2 + k * β ^ 2 + 2 * (k + 1) * α * β ≤ 6 := by
  have hk0 : 0 ≤ k := le_trans zero_le_one hk
  have hα1 : α ≤ 1 := by nlinarith [mul_nonneg hk0 hβ]
  have hkβ : k * β ≤ 1 := by linarith
  have hβ1 : β ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hβ]
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have hb2 : k * β ^ 2 ≤ 1 := calc
    _ = (k * β) * β := by ring
    _ ≤ 1 * 1 := mul_le_mul hkβ hβ1 hβ (by norm_num)
    _ = 1 := by ring
  have hab : α * β ≤ 1 := by simpa using mul_le_mul hα1 hβ1 hβ (by norm_num : (0 : ℝ) ≤ 1)
  have hkab : k * α * β ≤ 1 := calc
    _ = α * (k * β) := by ring
    _ ≤ 1 * 1 := mul_le_mul hα1 hkβ (mul_nonneg hk0 hβ) (by norm_num)
    _ = 1 := by ring
  nlinarith

/-- A convergent off-diagonal statistic and a fixed diagonal bound give
an actual finite stage and sample size with expected cost at most ten. -/
theorem exists_stage_sample_cost_le_ten
    (C : ℕ → ℕ → ℝ) (T : ℕ → ℝ) {D L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ 6) (hT : Tendsto T atTop (𝓝 L))
    (hC : ∀ j m, 1 ≤ m →
      C j m ≤ 1 + D / m + (1 - (m : ℝ)⁻¹) * T j) :
    ∃ j m, 1 ≤ m ∧ C j m ≤ 10 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max D 1)
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := lt_trans zero_lt_one hm1
  have hmNat : 1 ≤ m := by exact_mod_cast hm1.le
  have hD : D / m ≤ 1 := (div_le_one hmpos).mpr (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hm))
  have hnear : ∀ᶠ j in atTop, T j ∈ Set.Ioo (-7) 7 :=
    hT.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨j, hj⟩ := hnear.exists
  have habs : |T j| ≤ 7 := abs_le.mpr ⟨hj.1.le, hj.2.le⟩
  have hinv : (m : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hm1.le
  have hc0 : 0 ≤ 1 - (m : ℝ)⁻¹ := sub_nonneg.mpr hinv
  have hc1 : 1 - (m : ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr hmpos.le)
  have hterm : (1 - (m : ℝ)⁻¹) * T j ≤ 7 := calc
    _ ≤ (1 - (m : ℝ)⁻¹) * |T j| := mul_le_mul_of_nonneg_left (le_abs_self _) hc0
    _ ≤ 1 * 7 := mul_le_mul hc1 habs (abs_nonneg _) (by norm_num)
    _ = 7 := by ring
  exact ⟨j, m, hmNat, by linarith [hC j m hmNat]⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixGraphMomentBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix samples with bounded graph cost

The matrix-stage centralizer identities preserve the two second moments
and the diagonal fourth moments. Relative irreducibility supplies the
mixed-moment limits. Thus the bound of ten is attained by an actual
finite stage and a finite independent sample family.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Taking adjoints exchanges the two independent matrix samples. -/
theorem star_matrixOrbitSample {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (x : H →L[ℂ] H) (g : MatrixOrbitIndex d) :
    star (matrixOrbitSample E x g) = matrixOrbitSample E (star x) g.swap := by
  simp only [matrixOrbitSample, unitaryDoubleOrbit, star_mul, star_star]
  noncomm_ring

private theorem state_conj_p0 (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (g : SignedPermutation (Fin d)) (x : H →L[ℂ] H) (hx : x ∈ M) :
    realVectorState Ω (unitaryConj (matrixUnitSignedRepresentation E g) x) =
      realVectorState Ω x := by
  let u := matrixUnitSignedRepresentation E g
  have hu : (u : H →L[ℂ] H) ∈ E.algebra := matrixUnitSignedRepresentation_mem E g
  have he := hc u hu (x * star (u : H →L[ℂ] H))
    (M.mul_mem hx (M.toStarSubalgebra.star_mem' (hEM hu)))
  apply congrArg Complex.re
  change inner ℂ Ω (((u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (x Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using he

/-- Every actual matrix sample has the original right second moment. -/
theorem matrixOrbit_right_second (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (g : MatrixOrbitIndex d) :
    realVectorState Ω (star (matrixOrbitSample E x g) * matrixOrbitSample E x g) =
      ‖x Ω‖ ^ 2 := by
  rw [matrixOrbitSample, unitaryDoubleOrbit_star_mul_self]
  rw [state_conj_p0 M Ω E hEM hc g.2 _ (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx)]
  exact realVectorState_star_mul_self Ω x

/-- The left second moment is preserved as well. -/
theorem matrixOrbit_left_second (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (g : MatrixOrbitIndex d) :
    realVectorState Ω (matrixOrbitSample E x g * star (matrixOrbitSample E x g)) =
      ‖star x Ω‖ ^ 2 := by
  have he := matrixOrbit_right_second M Ω E hEM hc (star x)
    (M.toStarSubalgebra.star_mem' hx) g.swap
  simpa only [← star_matrixOrbitSample, star_star] using he

section Limits

variable (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M)

include M hΩ hmono hEM hirr hc hx

/-- There is a genuine finite matrix stage and a positive sample size
whose independently sampled signed graph cost is at most ten. -/
theorem exists_matrixOrbit_graphCost_le_ten_oai {k : ℝ} (hk : 1 ≤ k)
    (hxnorm : ‖x Ω‖ ^ 2 + k * ‖star x Ω‖ ^ 2 = 1) :
    ∃ j m, 1 ≤ m ∧
      (𝔼 ω : Fin m → MatrixOrbitIndex (d j), 𝔼 ε : Fin m → Bool,
        graphMomentCost Ω k
          (normalizedFiniteSignSum (fun i => matrixOrbitSample (E j) x (ω i)) ε)) ≤ 10 := by
  let C : ℕ → ℕ → ℝ := fun j m =>
    𝔼 ω : Fin m → MatrixOrbitIndex (d j), 𝔼 ε : Fin m → Bool,
      graphMomentCost Ω k
        (normalizedFiniteSignSum (fun i => matrixOrbitSample (E j) x (ω i)) ε)
  let T : ℕ → ℝ := fun j =>
    orbitFirstPairMoment Ω (matrixOrbitSample (E j) x) +
    2 * orbitThirdPairMoment Ω (matrixOrbitSample (E j) x) +
    k * (orbitFirstPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) +
      2 * orbitThirdPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)))
  let L := (‖x Ω‖ ^ 2) ^ 2 + k * (‖star x Ω‖ ^ 2) ^ 2 +
    2 * (k + 1) * ‖x Ω‖ ^ 2 * ‖star x Ω‖ ^ 2
  let D := realVectorState Ω ((star x * x) ^ 2) +
    k * realVectorState Ω ((x * star x) ^ 2)
  have hk0 : 0 ≤ k := le_trans zero_le_one hk
  have hL0 : 0 ≤ L := by dsimp [L] <;> positivity
  have hL6 : L ≤ 6 := graph_pairing_scalar_le_six (sq_nonneg _) (sq_nonneg _) hk hxnorm.le
  have hT : Tendsto T atTop (𝓝 L) :=
    matrixOrbit_graphPairing_tendsto M Ω hΩ d E hmono hEM hirr hc x hx k
  have hC (j m : ℕ) (hm : 1 ≤ m) :
      C j m ≤ 1 + D / m + (1 - (m : ℝ)⁻¹) * T j := by
    have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    let : NeZero m := ⟨Nat.ne_of_gt hm0⟩
    have hb := expect_sampled_graphMomentCost_le (I := Fin m) Ω hk0
      (matrixOrbitSample (E j) x)
    have hsecond : orbitSecondMoment Ω k (matrixOrbitSample (E j) x) = 1 := by
      unfold orbitSecondMoment
      simp only [matrixOrbit_right_second M Ω (E j) (hEM j) (hc j) x hx,
        matrixOrbit_left_second M Ω (E j) (hEM j) (hc j) x hx, Fintype.expect_const]
      exact hxnorm
    have hdiag : orbitDiagonalMoment Ω (matrixOrbitSample (E j) x) =
        realVectorState Ω ((star x * x) ^ 2) := by
      unfold orbitDiagonalMoment
      simp only [matrixOrbit_diagonal_fourth M Ω (E j) (hEM j) (hc j) x hx,
        Fintype.expect_const]
    have hdiagstar : orbitDiagonalMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) =
        realVectorState Ω ((x * star x) ^ 2) := by
      have hh (g : MatrixOrbitIndex (d j)) :=
        matrixOrbit_diagonal_fourth M Ω (E j) (hEM j) (hc j) (star x)
          (M.toStarSubalgebra.star_mem' hx) g.swap
      have hv (g : MatrixOrbitIndex (d j)) :
          realVectorState Ω ((star (star (matrixOrbitSample (E j) x g)) *
            star (matrixOrbitSample (E j) x g)) ^ 2) =
          realVectorState Ω ((x * star x) ^ 2) := by
        simpa only [← star_matrixOrbitSample, star_star] using hh g
      simp only [orbitDiagonalMoment, hv, Fintype.expect_const]
    simpa only [C, T, D, hsecond, hdiag, hdiagstar, Fintype.card_fin] using hb
  exact exists_stage_sample_cost_le_ten C T hL0 hL6 hT hC

end Limits

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_matrixOrbit_graphCost_le_ten_oai.{u_1} := @OAI.KadisonKastler.exists_matrixOrbit_graphCost_le_ten_oai.{u_1}
