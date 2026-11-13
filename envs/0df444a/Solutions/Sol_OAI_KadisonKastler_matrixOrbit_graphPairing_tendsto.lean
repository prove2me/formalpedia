-- Prove2me | solution 1 for OAI.KadisonKastler.matrixOrbit_graphPairing_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:16:20.328734+00:00
-- url     : https://prove2.me/submissions/62b4b687-5fa7-4c41-bd2b-3769342338b5

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

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The mixed positive square exposes the relative left conjugation. -/
theorem unitaryDoubleOrbit_mixed_square (x : H →L[ℂ] H)
    (u v u' v' : unitary (H →L[ℂ] H)) :
    (star (unitaryDoubleOrbit x u v) * unitaryDoubleOrbit x u' v') *
        (star (unitaryDoubleOrbit x u' v') * unitaryDoubleOrbit x u v) =
      unitaryConj v (star x * unitaryConj (star u)
        (unitaryConj u' (x * star x)) * x) := by
  simp only [unitaryDoubleOrbit, unitaryConj, star_mul, star_star, Unitary.coe_star]
  calc
    _ = (v : H →L[ℂ] H) * star x * star (u : H →L[ℂ] H) *
        (u' : H →L[ℂ] H) * x *
        (star (v' : H →L[ℂ] H) * (v' : H →L[ℂ] H)) *
        star x * star (u' : H →L[ℂ] H) * (u : H →L[ℂ] H) *
        x * star (v : H →L[ℂ] H) := by noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem v'.property]; noncomm_ring

private theorem state_conjugation (M : VonNeumannAlgebra H) (Ω : H)
    (v : unitary (H →L[ℂ] H)) (hv : (v : H →L[ℂ] H) ∈ M)
    (hc : ∀ z ∈ M, inner ℂ Ω (((v : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (v : H →L[ℂ] H)) Ω))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    operatorVectorState Ω (unitaryConj v a) = operatorVectorState Ω a := by
  have h := hc (a * star (v : H →L[ℂ] H))
    (M.mul_mem ha (M.toStarSubalgebra.star_mem' hv))
  change inner ℂ Ω (((v : H →L[ℂ] H) * a * star (v : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (a Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem v.property, mul_one] using h

/-- Removing the right conjugation from the vector state identifies the
third pairing for two actual orbit samples. -/
theorem vectorState_unitaryDoubleOrbit_mixed_square
    (M : VonNeumannAlgebra H) (Ω : H) (x : H →L[ℂ] H) (hx : x ∈ M)
    (u v u' v' : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) (hv : (v : H →L[ℂ] H) ∈ M)
    (hu' : (u' : H →L[ℂ] H) ∈ M)
    (hc : ∀ z ∈ M, inner ℂ Ω (((v : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (v : H →L[ℂ] H)) Ω)) :
    operatorVectorState Ω
      ((star (unitaryDoubleOrbit x u v) * unitaryDoubleOrbit x u' v') *
        (star (unitaryDoubleOrbit x u' v') * unitaryDoubleOrbit x u v)) =
      operatorVectorState Ω (star x * unitaryConj (star u)
        (unitaryConj u' (x * star x)) * x) := by
  rw [unitaryDoubleOrbit_mixed_square]
  apply state_conjugation M Ω v hv hc
  have hsx := M.toStarSubalgebra.star_mem' hx
  have hsu := M.toStarSubalgebra.star_mem' hu
  have hsu' := M.toStarSubalgebra.star_mem' hu'
  simp only [unitaryConj, Unitary.coe_star, star_star]
  change star x * ((star (u : H →L[ℂ] H)) *
    ((u' : H →L[ℂ] H) * (x * star x) * star (u' : H →L[ℂ] H)) *
      (u : H →L[ℂ] H)) * x ∈ M
  exact M.mul_mem (M.mul_mem hsx
    (M.mul_mem (M.mul_mem hsu
      (M.mul_mem (M.mul_mem hu' (M.mul_mem hx hsx)) hsu')) hu)) hx

/-- Averaging the first pairing over the four independent matrix samples
is precisely the first scalar expression of `MatrixStateMoments`. -/
theorem matrixOrbit_first_pairing_average
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    finiteAverage (fun i : SignedPermutation (Fin d) =>
      finiteAverage (fun j : SignedPermutation (Fin d) =>
        finiteAverage (fun k : SignedPermutation (Fin d) =>
          finiteAverage (fun l : SignedPermutation (Fin d) =>
            operatorVectorState Ω
              ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                (matrixUnitSignedRepresentation E j)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                  (matrixUnitSignedRepresentation E j)) *
               (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                (matrixUnitSignedRepresentation E l)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                  (matrixUnitSignedRepresentation E l))))))) =
      operatorVectorState Ω ((star x * x) * matrixUnitAverage E (star x * x)) := by
  simp only [unitaryDoubleOrbit_star_mul_self, finiteAverage_const]
  exact matrixState_two_orbit_average M Ω E hEM hc (star x * x) (star x * x)
    (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx)
    (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx)

/-- Averaging the third pairing over four independent matrix samples
reduces to the relative left-unitary average sandwiched by `x*` and `x`. -/
theorem matrixOrbit_third_pairing_average
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    finiteAverage (fun i : SignedPermutation (Fin d) =>
      finiteAverage (fun j : SignedPermutation (Fin d) =>
        finiteAverage (fun k : SignedPermutation (Fin d) =>
          finiteAverage (fun l : SignedPermutation (Fin d) =>
            operatorVectorState Ω
              ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                (matrixUnitSignedRepresentation E j)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                  (matrixUnitSignedRepresentation E l)) *
               (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                (matrixUnitSignedRepresentation E l)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                  (matrixUnitSignedRepresentation E j))))))) =
      operatorVectorState Ω (star x * matrixUnitAverage E (x * star x) * x) := by
  have he (i j k l : SignedPermutation (Fin d)) :=
    vectorState_unitaryDoubleOrbit_mixed_square M Ω x hx
      (matrixUnitSignedRepresentation E i) (matrixUnitSignedRepresentation E j)
      (matrixUnitSignedRepresentation E k) (matrixUnitSignedRepresentation E l)
      (hEM (matrixUnitSignedRepresentation_mem E i))
      (hEM (matrixUnitSignedRepresentation_mem E j))
      (hEM (matrixUnitSignedRepresentation_mem E k))
      (hc _ (matrixUnitSignedRepresentation_mem E j))
  simp only [he, finiteAverage_const]
  exact matrixState_relative_orbit_average Ω E (star x) (x * star x) x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixOrbitSampleLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

private theorem complex_expect_eq_average {G : Type*} [Fintype G] (f : G → ℂ) :
    (𝔼 g, f g) = finiteAverage f := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [finiteAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem re_average {G : Type*} [Fintype G] (f : G → ℂ) :
    (finiteAverage f).re = 𝔼 g, (f g).re := by
  rw [← complex_expect_eq_average]
  exact map_expect (Complex.reLm.restrictScalars ℚ≥0) f Finset.univ

private theorem expect_prod {G K : Type*} [Fintype G] [Fintype K]
    (f : G × K → ℝ) : (𝔼 p, f p) = 𝔼 g, 𝔼 k, f (g, k) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset G) (Finset.univ : Finset K) f

/-- The first off-diagonal moment is the actual first independent-copy
matrix pairing, expressed as a real number. -/
theorem matrixOrbit_first_pairing_expect
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    (𝔼 g : MatrixOrbitIndex d, 𝔼 h : MatrixOrbitIndex d,
      realVectorState Ω ((star (matrixOrbitSample E x g) * matrixOrbitSample E x g) *
        (star (matrixOrbitSample E x h) * matrixOrbitSample E x h))) =
      realVectorState Ω ((star x * x) * matrixUnitAverage E (star x * x)) := by
  rw [expect_prod]
  simp_rw [expect_prod]
  change (𝔼 i, 𝔼 j, 𝔼 k, 𝔼 l,
    (operatorVectorState Ω
      ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
        (matrixUnitSignedRepresentation E j)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
          (matrixUnitSignedRepresentation E j)) *
       (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
        (matrixUnitSignedRepresentation E l)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
          (matrixUnitSignedRepresentation E l)))).re) = _
  simp_rw [← re_average]
  rw [matrixOrbit_first_pairing_average M Ω E hEM hc x hx]
  rfl

/-- The positive mixed pairing similarly becomes one averaged left
square between `x*` and `x`. -/
theorem matrixOrbit_third_pairing_expect
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    (𝔼 g : MatrixOrbitIndex d, 𝔼 h : MatrixOrbitIndex d,
      realVectorState Ω ((star (matrixOrbitSample E x g) * matrixOrbitSample E x h) *
        (star (matrixOrbitSample E x h) * matrixOrbitSample E x g))) =
      realVectorState Ω (star x * matrixUnitAverage E (x * star x) * x) := by
  rw [expect_prod]
  simp_rw [expect_prod]
  change (𝔼 i, 𝔼 j, 𝔼 k, 𝔼 l,
    (operatorVectorState Ω
      ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
        (matrixUnitSignedRepresentation E j)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
          (matrixUnitSignedRepresentation E l)) *
       (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
        (matrixUnitSignedRepresentation E l)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
          (matrixUnitSignedRepresentation E j)))).re) = _
  simp_rw [← re_average]
  rw [matrixOrbit_third_pairing_average M Ω E hEM hc x hx]
  rfl

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
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixGraphMomentBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

private theorem expect_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (f : G → ℝ) : (𝔼 g, f (e g)) = 𝔼 g, f g :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

private theorem expect_pair_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (f : G → G → ℝ) :
    (𝔼 g, 𝔼 h, f (e g) (e h)) = 𝔼 g, 𝔼 h, f g h := by
  have hi (g : G) : (𝔼 h, f (e g) (e h)) = 𝔼 h, f (e g) h :=
    expect_comp_equiv e (f (e g))
  simp_rw [hi]
  exact expect_comp_equiv e (fun g => 𝔼 h, f g h)

private theorem firstMoment_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (Ω : H) (a : G → H →L[ℂ] H) :
    orbitFirstPairMoment Ω (fun g => a (e g)) = orbitFirstPairMoment Ω a :=
  expect_pair_comp_equiv e (fun g h =>
    realVectorState Ω ((star (a g) * a g) * (star (a h) * a h)))

private theorem thirdMoment_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (Ω : H) (a : G → H →L[ℂ] H) :
    orbitThirdPairMoment Ω (fun g => a (e g)) = orbitThirdPairMoment Ω a :=
  expect_pair_comp_equiv e (fun g h =>
    realVectorState Ω ((star (a g) * a h) * (star (a h) * a g)))

/-- Taking adjoints exchanges the two independent matrix samples. -/
theorem star_matrixOrbitSample {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (x : H →L[ℂ] H) (g : MatrixOrbitIndex d) :
    star (matrixOrbitSample E x g) = matrixOrbitSample E (star x) g.swap := by
  simp only [matrixOrbitSample, unitaryDoubleOrbit, star_mul, star_star]
  noncomm_ring

private theorem left_positive_state (Ω : H) (x : H →L[ℂ] H) :
    operatorVectorState Ω (x * star x) = (‖star x Ω‖ ^ 2 : ℝ) := by
  simpa only [star_star] using operatorVectorState_star_mul_self Ω (star x)

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

/-- The first actual sample pairing converges to the square of its
right second moment. -/
theorem matrixOrbit_firstMoment_tendsto :
    Tendsto (fun j => orbitFirstPairMoment Ω (matrixOrbitSample (E j) x)) atTop
      (𝓝 ((‖x Ω‖ ^ 2) ^ 2)) := by
  have hs := M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx
  have ht := matrixState_two_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (star x * x) (star x * x) hs hs
  simp_rw [matrixState_two_orbit_average M Ω _ (hEM _) (hc _) _ _ hs hs] at ht
  rw [operatorVectorState_star_mul_self] at ht
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp_rw [orbitFirstPairMoment, matrixOrbit_first_pairing_expect M Ω _ (hEM _) (hc _) x hx]
  simpa only [Function.comp_def, realVectorState_apply, operatorVectorState_apply,
    operatorVectorState_star_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, pow_two] using hr

/-- The positive mixed pairing converges to the product of the right
and left second moments. -/
theorem matrixOrbit_thirdMoment_tendsto :
    Tendsto (fun j => orbitThirdPairMoment Ω (matrixOrbitSample (E j) x)) atTop
      (𝓝 (‖x Ω‖ ^ 2 * ‖star x Ω‖ ^ 2)) := by
  have hs := M.mul_mem hx (M.toStarSubalgebra.star_mem' hx)
  have ht := matrixState_relative_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (star x) (x * star x) x hs
  simp_rw [matrixState_relative_orbit_average] at ht
  rw [left_positive_state, operatorVectorState_star_mul_self] at ht
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp_rw [orbitThirdPairMoment, matrixOrbit_third_pairing_expect M Ω _ (hEM _) (hc _) x hx]
  simpa only [Function.comp_def, operatorVectorState_star_mul_self, left_positive_state,
    ← Complex.ofReal_mul, Complex.ofReal_re, realVectorState_apply, operatorVectorState_apply,
    mul_comm] using hr

/-- The full off-diagonal cost has its required actual scalar limit. -/
theorem matrixOrbit_graphPairing_tendsto_oai (k : ℝ) :
    Tendsto (fun j =>
      orbitFirstPairMoment Ω (matrixOrbitSample (E j) x) +
      2 * orbitThirdPairMoment Ω (matrixOrbitSample (E j) x) +
      k * (orbitFirstPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) +
        2 * orbitThirdPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)))) atTop
      (𝓝 ((‖x Ω‖ ^ 2) ^ 2 + k * (‖star x Ω‖ ^ 2) ^ 2 +
        2 * (k + 1) * ‖x Ω‖ ^ 2 * ‖star x Ω‖ ^ 2)) := by
  have hr := matrixOrbit_firstMoment_tendsto M Ω hΩ d E hmono hEM hirr hc x hx
  have hm := matrixOrbit_thirdMoment_tendsto M Ω hΩ d E hmono hEM hirr hc x hx
  have hstar := M.toStarSubalgebra.star_mem' hx
  have hl := matrixOrbit_firstMoment_tendsto M Ω hΩ d E hmono hEM hirr hc (star x) hstar
  have hn := matrixOrbit_thirdMoment_tendsto M Ω hΩ d E hmono hEM hirr hc (star x) hstar
  have he1 (j : ℕ) :
      orbitFirstPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) =
        orbitFirstPairMoment Ω (matrixOrbitSample (E j) (star x)) := by
    simp_rw [star_matrixOrbitSample]
    exact firstMoment_comp_equiv (Equiv.prodComm _ _) Ω _
  have he3 (j : ℕ) :
      orbitThirdPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) =
        orbitThirdPairMoment Ω (matrixOrbitSample (E j) (star x)) := by
    simp_rw [star_matrixOrbitSample]
    exact thirdMoment_comp_equiv (Equiv.prodComm _ _) Ω _
  simp_rw [he1, he3]
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hk : Tendsto (fun _ : ℕ => k) atTop (𝓝 k) := tendsto_const_nhds
  have hlim := (hr.add (htwo.mul hm)).add (hk.mul (hl.add (htwo.mul hn)))
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [star_star]
  ring

end Limits

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.matrixOrbit_graphPairing_tendsto_oai.{u_1} := @OAI.KadisonKastler.matrixOrbit_graphPairing_tendsto_oai.{u_1}
