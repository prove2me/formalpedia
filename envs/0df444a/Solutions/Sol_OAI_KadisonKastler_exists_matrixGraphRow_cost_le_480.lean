-- Prove2me | solution 1 for OAI.KadisonKastler.exists_matrixGraphRow_cost_le_480
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:08:37.559439+00:00
-- url     : https://prove2.me/submissions/3b56a944-0115-45f7-b7ca-1ecf2cb233b8

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K012
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite averages of unitary conjugations -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {G : Type*} [Fintype G] [Nonempty G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem norm_finiteAverage_le (f : G → V) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) :
    ‖finiteAverage f‖ ≤ C := by
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g, f g‖ := by
      simp [finiteAverage, norm_smul, norm_inv]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _ : G, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun g _ => hf g)) (inv_nonneg.mpr hn.le)
    _ = C := by simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Group G]

omit [Nonempty G] in
theorem finiteUnitaryAverage_invariant (π : G →* unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) (g : G) :
    unitaryConj (π g) (finiteUnitaryAverage π h) = finiteUnitaryAverage π h := by
  have he : (∑ k : G, unitaryConj (π (g * k)) h) = ∑ k : G, unitaryConj (π k) h :=
    Equiv.sum_comp (Equiv.mulLeft g) (fun k => unitaryConj (π k) h)
  simp only [map_mul, unitaryConj_mul] at he
  unfold finiteUnitaryAverage finiteAverage
  simp only [unitaryConj, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1

omit [Nonempty G] in
theorem finiteUnitaryAverage_commutes (π : G →* unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) (g : G) :
    Commute (π g : H →L[ℂ] H) (finiteUnitaryAverage π h) := by
  have hh := congrArg (fun a : H →L[ℂ] H => a * (π g : H →L[ℂ] H))
    (finiteUnitaryAverage_invariant π h g)
  have hs := Unitary.star_mul_self_of_mem (π g).property
  change (π g : H →L[ℂ] H) * finiteUnitaryAverage π h =
    finiteUnitaryAverage π h * (π g : H →L[ℂ] H)
  simpa only [unitaryConj, mul_assoc, hs, mul_one] using hh


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteIndependentSamples
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging over a concrete finite matrix algebra

Signed permutation matrices give a finite unitary group whose commutant
is exactly the commutant of the matrix-unit system. Its uniform average
preserves the original scalar derivation bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A]
  [StarRing A]
  [_root_.Algebra ℂ A]
  [StarModule ℂ A]

omit [Fintype ι] in
/-- Changing one diagonal sign isolates the corresponding diagonal matrix unit. -/
theorem signDiagonal_reflection (i : ι) :
    signDiagonal (Function.update (1 : ι → ℤˣ) i (-1)) =
      1 - (2 : ℂ) • Matrix.single i i 1 := by
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i
    · subst j
      norm_num [signDiagonal, Matrix.diagonal, Matrix.single]
    · simp [signDiagonal, Matrix.diagonal, Matrix.single, hji, Ne.symm hji]
  · have hn : ¬ (i = j ∧ i = k) := fun h => hjk (h.1.symm.trans h.2)
    simp [signDiagonal, Matrix.diagonal, Matrix.single, hjk, hn]

theorem matrixUnit_diagonal_sandwich (E : Generator.MatrixUnitSystem ι A)
    (a : Matrix ι ι ℂ) (i j : ι) :
    E.entry i i * E.hom a * E.entry j j = a i j • E.entry i j := by
  simp only [Generator.MatrixUnitSystem.hom_apply, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, E.mul_entry]
  simp [E.mul_entry, smul_ite]

/-- Commuting with the finite signed-permutation group is enough to commute
with the entire full matrix algebra. -/
theorem commute_matrixUnits_of_signed (E : Generator.MatrixUnitSystem ι A) (x : A)
    (hx : ∀ g, Commute (matrixUnitSignedRepresentation E g : A) x) :
    ∀ i j, Commute (E.entry i j) x := by
  have hd (i : ι) : Commute (E.entry i i) x := by
    have hi := hx (SemidirectProduct.inl (Function.update (1 : ι → ℤˣ) i (-1)))
    rw [matrixUnitSignedRepresentation_inl, signDiagonal_reflection, map_sub, map_one,
      map_smul, E.hom_single, one_smul] at hi
    change (1 - (2 : ℂ) • E.entry i i) * x = x * (1 - (2 : ℂ) • E.entry i i) at hi
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm] at hi
    exact (smul_right_injective A (by norm_num : (2 : ℂ) ≠ 0)) (sub_right_inj.mp hi)
  have hp (σ : Equiv.Perm ι) : Commute (E.hom (Matrix.permMatrixHom (R := ℂ) σ)) x := by
    simpa only [matrixUnitSignedRepresentation_inr] using hx (SemidirectProduct.inr σ)
  intro i j
  have h := ((hd i).mul_left (hp (Equiv.swap i j))).mul_left (hd j)
  simpa only [matrixUnit_diagonal_sandwich, permutationMatrix_apply,
    Equiv.swap_apply_right, ↓reduceIte, one_smul] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matrixUnitAverage_commutes (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H))
    (h : H →L[ℂ] H) : ∀ a ∈ E.algebra, Commute a (matrixUnitAverage E h) := by
  apply (E.commute_algebra_iff _).mpr
  exact commute_matrixUnits_of_signed E _ (finiteUnitaryAverage_commutes _ h)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairIrreducibility
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative irreducibility survives a nearby common matrix algebra

Finite signed-permutation averages over increasing matrix algebras have
bounded weak operator cluster points. Such a cluster point commutes with
every stage. Relative irreducibility in the first algebra makes it scalar;
the norm ball around a relative projection in the neighbor survives the
averages and their limit. No trace, invariant mean or averaging limit is
assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A bounded weak cluster point of the concrete stage averages commutes
with every fixed stage. -/
theorem matrixUnitAverage_weak_limit_commutes
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (x T : H →L[ℂ] H) {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hlim : ∀ ξ η, Tendsto (fun n => inner ℂ η (matrixUnitAverage (E n) x ξ)) l
      (𝓝 (inner ℂ η (T ξ)))) :
    ∀ n a, a ∈ (E n).algebra → a * T = T * a := by
  intro n a ha
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have he : (fun j => inner ℂ (star a η) (matrixUnitAverage (E j) x ξ)) =ᶠ[l]
      (fun j => inner ℂ η (matrixUnitAverage (E j) x (a ξ))) := by
    filter_upwards [(eventually_ge_atTop n).filter_mono hl] with j hj
    have hc := (matrixUnitAverage_commutes (E j) x a (hmono hj ha)).eq
    have h := congrArg (fun B : H →L[ℂ] H => inner ℂ η (B ξ)) hc
    simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] using h
  have hleft := (hlim ξ (star a η)).congr' he
  have hright := hlim (a ξ) η
  have h := tendsto_nhds_unique hleft hright
  simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStateAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix averages in the centralizer of a vector state

Finite signed-permutation averages preserve a vector state centralizing
the matrix stages. Their bounded weak cluster points are scalar by
relative irreducibility. State preservation identifies each scalar, and
the ultrafilter criterion then gives actual weak convergence of the whole
sequence. No traciality of the ambient algebra is required.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Each finite average preserves the vector state when its unitary
matrix group lies in the state's centralizer. -/
theorem matrixUnitAverage_preserves_vectorFunctional
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hcentral : ∀ a ∈ E.algebra, ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    inner ℂ Ω (matrixUnitAverage E x Ω) = inner ℂ Ω (x Ω) := by
  let φ := ambientVectorFunctional Ω
  have hconj (g : SignedPermutation (Fin d)) :
      φ (unitaryConj (matrixUnitSignedRepresentation E g) x) = φ x := by
    let u := matrixUnitSignedRepresentation E g
    have hu : (u : H →L[ℂ] H) ∈ E.algebra := matrixUnitSignedRepresentation_mem E g
    have hc := hcentral u hu (x * star (u : H →L[ℂ] H))
      (M.mul_mem hx (M.toStarSubalgebra.star_mem' (hEM hu)))
    change inner ℂ Ω (((u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) Ω) =
      inner ℂ Ω (x Ω)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using hc
  change φ (finiteAverage (fun g => unitaryConj (matrixUnitSignedRepresentation E g) x)) = φ x
  have hmap : φ (finiteAverage (fun g => unitaryConj (matrixUnitSignedRepresentation E g) x)) =
      finiteAverage (fun g : SignedPermutation (Fin d) =>
        φ (unitaryConj (matrixUnitSignedRepresentation E g) x)) := by
    simp only [finiteAverage, map_smul, map_sum]
  rw [hmap]
  simpa only [hconj] using (finiteAverage_const (G := SignedPermutation (Fin d)) (φ x))

private theorem stateAverage_norm_le {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖matrixUnitAverage E x‖ ≤ ‖x‖ := by
  apply norm_finiteAverage_le
  intro g
  exact (norm_unitaryConj (matrixUnitSignedRepresentation E g) x).le

theorem matrixUnitAverage_mem_algebra {d : ℕ} (M : VonNeumannAlgebra H)
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (x : H →L[ℂ] H) (hx : x ∈ M) : matrixUnitAverage E x ∈ M := by
  change (Fintype.card (SignedPermutation (Fin d)) : ℂ)⁻¹ •
    ∑ g : SignedPermutation (Fin d),
      ((matrixUnitSignedRepresentation E g : H →L[ℂ] H) * x *
        star (matrixUnitSignedRepresentation E g : H →L[ℂ] H)) ∈ M
  apply M.toStarSubalgebra.smul_mem
  apply M.toStarSubalgebra.sum_mem
  intro g _
  exact M.mul_mem (M.mul_mem (hEM (matrixUnitSignedRepresentation_mem E g)) hx)
    (M.toStarSubalgebra.star_mem' (hEM (matrixUnitSignedRepresentation_mem E g)))

/-- The entire sequence of concrete matrix averages converges weakly to
the scalar determined by the normalized vector state. -/
theorem matrixUnitAverage_tendsto_vectorState
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (ξ η : H) :
    Tendsto (fun n => inner ℂ η (matrixUnitAverage (E n) x ξ)) atTop
      (𝓝 (inner ℂ η (((inner ℂ Ω (x Ω)) • (1 : H →L[ℂ] H)) ξ))) := by
  apply (tendsto_iff_ultrafilter _ _ _).mpr
  intro ω hω
  let f : ℕ → H →L[ℂ] H := fun n => matrixUnitAverage (E n) x
  obtain ⟨T, _, hlim⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω f ‖x‖
    (norm_nonneg x) (fun n => stateAverage_norm_le (E n) x)
  have hTM : T ∈ M := Generator.Tracial.weak_operator_limit_mem M
    (fun n => ⟨f n, matrixUnitAverage_mem_algebra M (E n) (hEM n) x hx⟩) T hlim
  obtain ⟨z, hz⟩ := hirr T hTM
    (matrixUnitAverage_weak_limit_commutes d E hmono x T hω hlim)
  have hpreserve (n : ℕ) : inner ℂ Ω (f n Ω) = inner ℂ Ω (x Ω) :=
    matrixUnitAverage_preserves_vectorFunctional M Ω (E n) (hEM n) (hcentral n) x hx
  have hstate : inner ℂ Ω (T Ω) = inner ℂ Ω (x Ω) := by
    apply tendsto_nhds_unique (hlim Ω Ω)
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ Ω (x Ω))
      (ω : Filter ℕ) (𝓝 (inner ℂ Ω (x Ω)))).congr'
        (Eventually.of_forall fun n => (hpreserve n).symm)
  have hzstate : z = inner ℂ Ω (x Ω) := by
    rw [hz] at hstate
    simpa [smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ] using hstate
  simpa only [hz, hzstate] using hlim ξ η

/-- Weak coefficient convergence gives the corresponding sandwiched
vector-state limit, the form used for mixed fourth moments. -/
theorem vectorState_sandwich_tendsto
    {I : Type*} {l : Filter I} (F : I → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hlim : ∀ ξ η, Tendsto (fun i => inner ℂ η (F i ξ)) l (𝓝 (inner ℂ η (T ξ))))
    (Ω : H) (a b : H →L[ℂ] H) :
    Tendsto (fun i => inner ℂ Ω ((a * F i * b) Ω)) l
      (𝓝 (inner ℂ Ω ((a * T * b) Ω))) := by
  simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using hlim (b Ω) (star a Ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStateMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

private theorem average_linear {G V W : Type*} [Fintype G]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (L : V →ₗ[ℂ] W) (f : G → V) :
    finiteAverage (fun g => L (f g)) = L (finiteAverage f) := by
  simp only [finiteAverage, map_smul, map_sum]

private theorem average_sandwich {G : Type*} [Fintype G]
    (a b : H →L[ℂ] H) (f : G → H →L[ℂ] H) :
    finiteAverage (fun g => a * f g * b) = a * finiteAverage f * b := by
  simp only [finiteAverage, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]

private theorem state_unitaryConj (M : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M)
    (hcentral : ∀ z ∈ M, inner ℂ Ω (((u : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (u : H →L[ℂ] H)) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    operatorVectorState Ω (unitaryConj u x) = operatorVectorState Ω x := by
  have hc := hcentral (x * star (u : H →L[ℂ] H))
    (M.mul_mem hx (M.toStarSubalgebra.star_mem' hu))
  change inner ℂ Ω (((u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (x Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using hc

/-- The first pairing of two independently conjugated copies is exactly
one matrix average, paired against the unaveraged first element. -/
theorem matrixState_two_orbit_average
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hcentral : ∀ a ∈ E.algebra, ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) :
    finiteAverage (fun g : SignedPermutation (Fin d) =>
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω
          (unitaryConj (matrixUnitSignedRepresentation E g) a *
            unitaryConj (matrixUnitSignedRepresentation E h) b))) =
      operatorVectorState Ω (a * matrixUnitAverage E b) := by
  let B := matrixUnitAverage E b
  have hB : B ∈ M := matrixUnitAverage_mem_algebra M E hEM b hb
  have he (g : SignedPermutation (Fin d)) :
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω
          (unitaryConj (matrixUnitSignedRepresentation E g) a *
            unitaryConj (matrixUnitSignedRepresentation E h) b)) =
      operatorVectorState Ω (a * B) := by
    rw [average_linear]
    have hm : finiteAverage (fun h : SignedPermutation (Fin d) =>
        unitaryConj (matrixUnitSignedRepresentation E g) a *
          unitaryConj (matrixUnitSignedRepresentation E h) b) =
        unitaryConj (matrixUnitSignedRepresentation E g) a * B := by
      change finiteAverage (fun h : SignedPermutation (Fin d) =>
        unitaryConj (matrixUnitSignedRepresentation E g) a *
          unitaryConj (matrixUnitSignedRepresentation E h) b) =
        unitaryConj (matrixUnitSignedRepresentation E g) a *
          finiteAverage (fun h : SignedPermutation (Fin d) =>
            unitaryConj (matrixUnitSignedRepresentation E h) b)
      simpa only [mul_one] using average_sandwich (H := H)
        (unitaryConj (matrixUnitSignedRepresentation E g) a) 1
        (fun h => unitaryConj (matrixUnitSignedRepresentation E h) b)
    rw [hm]
    have hi : unitaryConj (matrixUnitSignedRepresentation E g) B = B :=
      finiteUnitaryAverage_invariant (H := H) (matrixUnitSignedRepresentation E) b g
    have hp : unitaryConj (matrixUnitSignedRepresentation E g) (a * B) =
        unitaryConj (matrixUnitSignedRepresentation E g) a * B := by
      have hmul := map_mul (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H)
        (matrixUnitSignedRepresentation E g)) a B
      change unitaryConj _ (a * B) = unitaryConj _ a * unitaryConj _ B at hmul
      rwa [hi] at hmul
    rw [← hp]
    exact state_unitaryConj M Ω _ (hEM (matrixUnitSignedRepresentation_mem E g))
      (hcentral _ (matrixUnitSignedRepresentation_mem E g)) (a * B) (M.mul_mem ha hB)
  simp only [he, finiteAverage_const]
  rfl

/-- Averaging a relative pair of independently sampled matrix unitaries
also gives the ordinary matrix average. -/
theorem matrixState_relative_orbit_average
    (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (a b c : H →L[ℂ] H) :
    finiteAverage (fun g : SignedPermutation (Fin d) =>
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω (a *
          unitaryConj (star (matrixUnitSignedRepresentation E g))
            (unitaryConj (matrixUnitSignedRepresentation E h) b) * c))) =
      operatorVectorState Ω (a * matrixUnitAverage E b * c) := by
  have he (g : SignedPermutation (Fin d)) :
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω (a *
          unitaryConj (star (matrixUnitSignedRepresentation E g))
            (unitaryConj (matrixUnitSignedRepresentation E h) b) * c)) =
      operatorVectorState Ω (a * matrixUnitAverage E b * c) := by
    rw [average_linear, average_sandwich]
    have hm : finiteAverage (fun h : SignedPermutation (Fin d) =>
        unitaryConj (star (matrixUnitSignedRepresentation E g))
          (unitaryConj (matrixUnitSignedRepresentation E h) b)) =
        unitaryConj (star (matrixUnitSignedRepresentation E g)) (matrixUnitAverage E b) := by
      change finiteAverage (fun h : SignedPermutation (Fin d) =>
        (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H) *
          unitaryConj (matrixUnitSignedRepresentation E h) b *
          star (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H)) =
        (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H) *
          finiteAverage (fun h : SignedPermutation (Fin d) =>
            unitaryConj (matrixUnitSignedRepresentation E h) b) *
          star (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H)
      exact average_sandwich (H := H) _ _ _
    rw [hm]
    have hi := finiteUnitaryAverage_invariant (H := H) (matrixUnitSignedRepresentation E) b g
    have hi' := congrArg (unitaryConj (star (matrixUnitSignedRepresentation E g))) hi
    rw [unitaryConj_star_unitaryConj] at hi'
    change matrixUnitAverage E b =
      unitaryConj (star (matrixUnitSignedRepresentation E g)) (matrixUnitAverage E b) at hi'
    rw [← hi']
  simp only [he, finiteAverage_const]

/-- The first independent-copy pairing tends to the product of the two
vector-state values. -/
theorem matrixState_two_orbit_tendsto
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) :
    Tendsto (fun n => finiteAverage (fun g : SignedPermutation (Fin (d n)) =>
      finiteAverage (fun h : SignedPermutation (Fin (d n)) =>
        operatorVectorState Ω (unitaryConj (matrixUnitSignedRepresentation (E n) g) a *
          unitaryConj (matrixUnitSignedRepresentation (E n) h) b)))) atTop
      (𝓝 (operatorVectorState Ω a * operatorVectorState Ω b)) := by
  simp_rw [matrixState_two_orbit_average M Ω _ (hEM _) (hcentral _) a b ha hb]
  have hl := vectorState_sandwich_tendsto (fun n => matrixUnitAverage (E n) b)
    ((operatorVectorState Ω b) • (1 : H →L[ℂ] H))
    (matrixUnitAverage_tendsto_vectorState M Ω hΩ d E hmono hEM hirr hcentral b hb)
    Ω a 1
  simpa only [mul_one, mul_smul_comm, mul_one, smul_apply, inner_smul_right,
    operatorVectorState_apply, mul_comm] using hl

/-- The nested relative-conjugation pairing tends to the scalar state
value of the averaged element times the state of the sandwich. -/
theorem matrixState_relative_orbit_tendsto
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (a b c : H →L[ℂ] H) (hb : b ∈ M) :
    Tendsto (fun n => finiteAverage (fun g : SignedPermutation (Fin (d n)) =>
      finiteAverage (fun h : SignedPermutation (Fin (d n)) =>
        operatorVectorState Ω (a * unitaryConj (star (matrixUnitSignedRepresentation (E n) g))
          (unitaryConj (matrixUnitSignedRepresentation (E n) h) b) * c)))) atTop
      (𝓝 (operatorVectorState Ω b * operatorVectorState Ω (a * c))) := by
  simp_rw [matrixState_relative_orbit_average]
  have hl := vectorState_sandwich_tendsto (fun n => matrixUnitAverage (E n) b)
    ((operatorVectorState Ω b) • (1 : H →L[ℂ] H))
    (matrixUnitAverage_tendsto_vectorState M Ω hΩ d E hmono hEM hirr hcentral b hb)
    Ω a c
  simpa only [mul_smul_comm, smul_mul_assoc, mul_one, smul_apply, inner_smul_right,
    operatorVectorState_apply] using hl

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
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphMomentBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The exact complex value of the positive vector-state square. -/
theorem operatorVectorState_star_mul_self (Ω : H) (x : H →L[ℂ] H) :
    operatorVectorState Ω (star x * x) = (‖x Ω‖ ^ 2 : ℝ) := by
  simp only [operatorVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphRowMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moments of a finite replicated graph row

The row consists of independently chosen left matrix translates of the
same clipped element. Its two fourth-moment sums reduce to the actual
matrix averages already shown to converge to the vector state.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem re_finiteAverage {G : Type*} [Fintype G] (f : G → ℂ) :
    (finiteAverage f).re = 𝔼 g, (f g).re := by
  have he : (𝔼 g, f g) = finiteAverage f := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [finiteAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [← he]
  exact map_expect (Complex.reLm.restrictScalars ℚ≥0) f Finset.univ

private theorem realState_conj (M : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M)
    (hc : ∀ x ∈ M, inner ℂ Ω (((u : H →L[ℂ] H) * x) Ω) =
      inner ℂ Ω ((x * (u : H →L[ℂ] H)) Ω))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    realVectorState Ω (unitaryConj u a) = realVectorState Ω a := by
  have h := hc (a * star (u : H →L[ℂ] H))
    (M.mul_mem ha (M.toStarSubalgebra.star_mem' hu))
  apply congrArg Complex.re
  change inner ℂ Ω (((u : H →L[ℂ] H) * a * star (u : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (a Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using h

private theorem leftTranslate_left_square (u : unitary (H →L[ℂ] H)) (z : H →L[ℂ] H) :
    ((u : H →L[ℂ] H) * z) * star ((u : H →L[ℂ] H) * z) =
      unitaryConj u (z * star z) := by
  simp only [unitaryConj, star_mul, mul_assoc]

private theorem leftTranslate_pair (u v : unitary (H →L[ℂ] H)) (z : H →L[ℂ] H) :
    star ((u : H →L[ℂ] H) * z) *
        (((v : H →L[ℂ] H) * z) * star ((v : H →L[ℂ] H) * z)) *
          ((u : H →L[ℂ] H) * z) =
      star z * unitaryConj (star u) (unitaryConj v (z * star z)) * z := by
  simp only [star_mul, unitaryConj, Unitary.coe_star, star_star]
  noncomm_ring

private theorem leftTranslate_pair_diagonal (u : unitary (H →L[ℂ] H))
    (z : H →L[ℂ] H) :
    star z * unitaryConj (star u) (unitaryConj u (z * star z)) * z =
      (star z * z) ^ 2 := by
  rw [unitaryConj_star_unitaryConj]
  noncomm_ring

/-- Expanding the actual row cost yields two independent pair sums. -/
theorem graphRowCost_eq_pair_sums (Ω : H) {I : Type*} [Fintype I]
    (Y : I → H →L[ℂ] H) :
    graphRowCost Ω Y =
      (∑ i, ∑ j, realVectorState Ω ((Y i * star (Y i)) * (Y j * star (Y j)))) +
      (Fintype.card I : ℝ)⁻¹ *
        ∑ i, ∑ j, realVectorState Ω (star (Y i) * (Y j * star (Y j)) * Y i) := by
  simp only [graphRowCost, graphRowSquare, pow_two, Finset.sum_mul,
    Finset.mul_sum, map_sum]
  congr 1
  exact Finset.sum_comm

/-- The finite independent sampling law gives the exact expected cost
of the replicated row, before any limiting estimate. -/
theorem expect_matrixGraphRow_cost (M : VonNeumannAlgebra H) (Ω : H)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (z : H →L[ℂ] H) (hz : z ∈ M) :
    (𝔼 ω : I → SignedPermutation (Fin d), graphRowCost Ω (matrixGraphRow E z ω)) =
      (Fintype.card I : ℝ) * realVectorState Ω ((z * star z) ^ 2) +
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) *
        realVectorState Ω ((z * star z) * matrixUnitAverage E (z * star z)) +
      realVectorState Ω ((star z * z) ^ 2) +
      ((Fintype.card I : ℝ) - 1) *
        realVectorState Ω (star z * matrixUnitAverage E (z * star z) * z) := by
  let u : SignedPermutation (Fin d) → unitary (H →L[ℂ] H) :=
    matrixUnitSignedRepresentation E
  let f : SignedPermutation (Fin d) → SignedPermutation (Fin d) → ℝ := fun g h =>
    realVectorState Ω (unitaryConj (u g) (z * star z) * unitaryConj (u h) (z * star z))
  let q : SignedPermutation (Fin d) → SignedPermutation (Fin d) → ℝ := fun g h =>
    realVectorState Ω (star z * unitaryConj (star (u g))
      (unitaryConj (u h) (z * star z)) * z)
  have hfdiag : (𝔼 g, f g g) = realVectorState Ω ((z * star z) ^ 2) := by
    have he (g : SignedPermutation (Fin d)) : f g g =
        realVectorState Ω ((z * star z) ^ 2) := by
      dsimp only [f]
      rw [← pow_two]
      have hp := map_pow (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (u g)) (z * star z) 2
      change unitaryConj (u g) ((z * star z) ^ 2) = (unitaryConj (u g) (z * star z)) ^ 2 at hp
      rw [← hp]
      exact realState_conj M Ω (u g) (hEM (matrixUnitSignedRepresentation_mem E g))
        (hc _ (matrixUnitSignedRepresentation_mem E g)) _
        (M.pow_mem (M.mul_mem hz (M.toStarSubalgebra.star_mem' hz)) 2)
    simp_rw [he]
    exact Fintype.expect_const _
  have hqdiag : (𝔼 g, q g g) = realVectorState Ω ((star z * z) ^ 2) := by
    simp only [q, leftTranslate_pair_diagonal, Fintype.expect_const]
  have hfpair : (𝔼 g, 𝔼 h, f g h) =
      realVectorState Ω ((z * star z) * matrixUnitAverage E (z * star z)) := by
    have h := congrArg Complex.re (matrixState_two_orbit_average M Ω E hEM hc
      (z * star z) (z * star z) (M.mul_mem hz (M.toStarSubalgebra.star_mem' hz))
      (M.mul_mem hz (M.toStarSubalgebra.star_mem' hz)))
    simp_rw [re_finiteAverage] at h
    exact h
  have hqpair : (𝔼 g, 𝔼 h, q g h) =
      realVectorState Ω (star z * matrixUnitAverage E (z * star z) * z) := by
    have h := congrArg Complex.re (matrixState_relative_orbit_average Ω E
      (star z) (z * star z) z)
    simp_rw [re_finiteAverage] at h
    exact h
  have he (ω : I → SignedPermutation (Fin d)) :
      graphRowCost Ω (matrixGraphRow E z ω) =
        (∑ i, ∑ j, f (ω i) (ω j)) +
          (Fintype.card I : ℝ)⁻¹ * ∑ i, ∑ j, q (ω i) (ω j) := by
    rw [graphRowCost_eq_pair_sums]
    simp only [matrixGraphRow]
    simp_rw [leftTranslate_pair, leftTranslate_left_square]
    rfl
  simp_rw [he]
  rw [Finset.expect_add_distrib, ← Finset.mul_expect,
    expect_sample_pair_sum, expect_sample_pair_sum, hfdiag, hqdiag, hfpair, hqpair]
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- A bounded operator controls the fourth vector-state moment by its
second moment, without a trace assumption. -/
theorem realVectorState_fourth_le_norm_sq (Ω : H) (z : H →L[ℂ] H) :
    realVectorState Ω ((star z * z) ^ 2) ≤ ‖z‖ ^ 2 * ‖z Ω‖ ^ 2 := by
  have he : (star z * z) ^ 2 = star (star z * z) * (star z * z) := by
    simp only [star_mul, star_star, pow_two]
  rw [he, realVectorState_star_mul_self, mul_apply_eq_comp]
  have hn := (star z).le_opNorm (z Ω)
  rw [norm_star] at hn
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [mul_pow] using hh

/-- The corresponding bound holds for the left square. -/
theorem realVectorState_reverse_fourth_le_norm_sq (Ω : H) (z : H →L[ℂ] H) :
    realVectorState Ω ((z * star z) ^ 2) ≤ ‖z‖ ^ 2 * ‖star z Ω‖ ^ 2 := by
  simpa only [star_star, norm_star] using realVectorState_fourth_le_norm_sq Ω (star z)

/-- The exact limiting cost of the independent replicated row. -/
theorem matrixGraphRow_cost_tendsto (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (z : H →L[ℂ] H) (hz : z ∈ M) :
    Tendsto (fun n => 𝔼 ω : I → SignedPermutation (Fin (d n)),
      graphRowCost Ω (matrixGraphRow (E n) z ω)) atTop
      (𝓝 ((Fintype.card I : ℝ) * realVectorState Ω ((z * star z) ^ 2) +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * ‖star z Ω‖ ^ 4 +
        realVectorState Ω ((star z * z) ^ 2) +
        ((Fintype.card I : ℝ) - 1) * (‖z Ω‖ ^ 2 * ‖star z Ω‖ ^ 2))) := by
  have hb : z * star z ∈ M := M.mul_mem hz (M.toStarSubalgebra.star_mem' hz)
  have hp := matrixState_two_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (z * star z) (z * star z) hb hb
  simp_rw [matrixState_two_orbit_average M Ω _ (hEM _) (hc _) _ _ hb hb] at hp
  have hq := matrixState_relative_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (star z) (z * star z) z hb
  simp_rw [matrixState_relative_orbit_average] at hq
  have hleft : operatorVectorState Ω (z * star z) = (‖star z Ω‖ ^ 2 : ℝ) := by
    simpa only [star_star] using operatorVectorState_star_mul_self Ω (star z)
  have hright : operatorVectorState Ω (star z * z) = (‖z Ω‖ ^ 2 : ℝ) :=
    operatorVectorState_star_mul_self Ω z
  rw [hleft] at hp
  rw [hleft, hright] at hq
  have hpR := Complex.continuous_re.tendsto _ |>.comp hp
  have hqR := Complex.continuous_re.tendsto _ |>.comp hq
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hpR hqR
  have hpR' : Tendsto (fun n => realVectorState Ω ((z * star z) *
      matrixUnitAverage (E n) (z * star z))) atTop (𝓝 (‖star z Ω‖ ^ 4)) := by
    rw [show ‖star z Ω‖ ^ 2 * ‖star z Ω‖ ^ 2 = ‖star z Ω‖ ^ 4 by ring] at hpR
    exact hpR
  change Tendsto (fun n => realVectorState Ω (star z *
      matrixUnitAverage (E n) (z * star z) * z)) atTop
    (𝓝 (‖star z Ω‖ ^ 2 * ‖z Ω‖ ^ 2)) at hqR
  rw [mul_comm (‖star z Ω‖ ^ 2) (‖z Ω‖ ^ 2)] at hqR
  simp_rw [expect_matrixGraphRow_cost M Ω _ (hEM _) (hc _) z hz]
  exact (((hpR'.const_mul ((Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1))).const_add
    ((Fintype.card I : ℝ) * realVectorState Ω ((z * star z) ^ 2))).add_const
      (realVectorState Ω ((star z * z) ^ 2))).add
        (hqR.const_mul ((Fintype.card I : ℝ) - 1))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform row flattening at arbitrary large rescalings

Rounding the squared rescaling up changes the moment normalization by at
most a factor two. The same fixed row cutoff remains sufficient.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem rowLimit_numeric_bound_480 {k α β D E : ℝ}
    (hk : 1 ≤ k) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsize : α + k * β ≤ 480)
    (hD : D ≤ 128 ^ 2 * β) (hE : E ≤ 128 ^ 2 * α) :
    k * D + k * (k - 1) * β ^ 2 + E + (k - 1) * (α * β) < 16777216 := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hb0 : 0 ≤ k * β := mul_nonneg hk0 hβ
  have ha1 : α ≤ 480 := by linarith
  have hb1 : k * β ≤ 480 := by linarith
  have hkd := mul_le_mul_of_nonneg_left hD hk0
  have hpair : k * (k - 1) * β ^ 2 ≤ (k * β) ^ 2 := by
    nlinarith [mul_nonneg hk0 (sq_nonneg β)]
  have hcross : (k - 1) * (α * β) ≤ α * (k * β) := by
    nlinarith [mul_nonneg hα hβ]
  have hbsq : (k * β) ^ 2 ≤ 480 ^ 2 := by nlinarith
  have hab : α * (k * β) ≤ 480 ^ 2 := by
    exact (mul_le_mul ha1 hb1 hb0 (by norm_num)).trans_eq (by norm_num)
  nlinarith

/-- For every flattened element, an actual finite matrix-orbit row has
uniformly bounded cost. The row length is exactly the square rescaling. -/
theorem exists_matrixGraphRow_cost_le_480_oai
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    {k : ℕ} (hk : 0 < k) (z : H →L[ℂ] H) (hz : z ∈ M)
    (hznorm : ‖z‖ ≤ 128) (hzsize : ‖z Ω‖ ^ 2 + k * ‖star z Ω‖ ^ 2 ≤ 480) :
    ∃ j, ∃ ω : Fin k → SignedPermutation (Fin (d j)),
      graphRowCost Ω (matrixGraphRow (E j) z ω) ≤ 16777216 := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hD := realVectorState_reverse_fourth_le_norm_sq Ω z
  have hF := realVectorState_fourth_le_norm_sq Ω z
  have hnorm2 : ‖z‖ ^ 2 ≤ (128 : ℝ) ^ 2 := by nlinarith [norm_nonneg z]
  have hD' : realVectorState Ω ((z * star z) ^ 2) ≤ 128 ^ 2 * ‖star z Ω‖ ^ 2 :=
    hD.trans (mul_le_mul_of_nonneg_right hnorm2 (sq_nonneg _))
  have hF' : realVectorState Ω ((star z * z) ^ 2) ≤ 128 ^ 2 * ‖z Ω‖ ^ 2 :=
    hF.trans (mul_le_mul_of_nonneg_right hnorm2 (sq_nonneg _))
  have hL := rowLimit_numeric_bound_480 (k := (k : ℝ)) (α := ‖z Ω‖ ^ 2)
    (β := ‖star z Ω‖ ^ 2) (by exact_mod_cast hk) (sq_nonneg _) (sq_nonneg _)
    hzsize hD' hF'
  have ht := matrixGraphRow_cost_tendsto M Ω hΩ (I := Fin k) d E hmono hEM hirr hc z hz
  simp only [Fintype.card_fin] at ht
  have hpow : ‖star z Ω‖ ^ 4 = (‖star z Ω‖ ^ 2) ^ 2 := by ring
  rw [hpow] at ht
  have he := ht.eventually (gt_mem_nhds hL)
  obtain ⟨j, hj⟩ := he.exists
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_expect_le
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin k → SignedPermutation (Fin (d j)))).Nonempty)
    hj.le
  exact ⟨j, ω, hω⟩


end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_matrixGraphRow_cost_le_480_oai.{u_1} := @OAI.KadisonKastler.exists_matrixGraphRow_cost_le_480_oai.{u_1}
