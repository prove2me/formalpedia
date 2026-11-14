-- Prove2me | solution 1 for OAI.KadisonKastler.relative_irreducibility_of_near_increasing_matrices
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:37:30.913597+00:00
-- url     : https://prove2.me/submissions/0eb7fd8e-2365-4cac-a1de-dab913545de1

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
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
import Definitions.Def_Q260K027

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

omit [Nonempty G] in
theorem finiteAverage_sub (f g : G → V) :
    finiteAverage (fun a => f a - g a) = finiteAverage f - finiteAverage g := by
  simp [finiteAverage, Finset.sum_sub_distrib, smul_sub]

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCenter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar orbit averages and central projections of a nearby algebra

Least vectors in the trace Hilbert space give scalar orbit averages in a
finite factor. Operator-norm balls centred at ambient operators are retained
under this averaging, even when their centre is outside the factor.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}


/-- A projection within one half of a scalar is trivial. -/
theorem projection_eq_zero_or_one_of_near_scalar {A : Type*} [CStarAlgebra A]
    (q : A) (hq : IsStarProjection q) (c : ℂ)
    (hclose : ‖c • (1 : A) - q‖ < 1 / 2) : q = 0 ∨ q = 1 := by
  by_contra hn
  push Not at hn
  have hnq : ‖q‖ = 1 := by
    have hh := (CStarRing.norm_star_mul_self (x := q))
    rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq] at hh
    nlinarith [norm_pos_iff.mpr hn.1]
  have hcomp : ‖1 - q‖ = 1 := by
    have hh := (CStarRing.norm_star_mul_self (x := 1 - q))
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq] at hh
    have hne : (1 : A) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hn.2)
    nlinarith [norm_pos_iff.mpr hne]
  have hmul : (c • (1 : A) - q) * q = (c - 1) • q := by
    simp only [sub_mul, smul_mul_assoc, one_mul, hq.isIdempotentElem.eq,
      sub_smul, one_smul]
  have hmul' : (c • (1 : A) - q) * (1 - q) = c • (1 - q) := by
    rw [sub_mul, smul_mul_assoc, one_mul, hq.mul_one_sub_self, sub_zero]
  have hc : ‖c‖ < 1 / 2 := by
    have h := norm_mul_le (c • (1 : A) - q) (1 - q)
    rw [hmul', norm_smul, hcomp, mul_one, mul_one] at h
    exact h.trans_lt hclose
  have hc1 : ‖c - 1‖ < 1 / 2 := by
    have h := norm_mul_le (c • (1 : A) - q) q
    rw [hmul, norm_smul, hnq, mul_one, mul_one] at h
    exact h.trans_lt hclose
  have htri := norm_sub_le c (c - 1)
  rw [sub_sub_cancel, norm_one] at htri
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- A uniform operator norm bound survives a weak coefficient limit. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  change (inner ℂ (S x) y).re ≤ C
  have hb (i : ι) : (inner ℂ y (T i x)).re ≤ C := by
    calc
      _ ≤ ‖inner ℂ y (T i x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T i).le_of_opNorm_le (hT i) x) (norm_nonneg y)
      _ = C := by rw [hx, hy]; ring
  have hr := (Complex.continuous_re.tendsto _).comp (ht x y)
  rw [show (inner ℂ (S x) y).re = (inner ℂ y (S x)).re from
    inner_re_symm (𝕜 := ℂ) (S x) y]
  exact le_of_tendsto hr (Eventually.of_forall hb)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairIrreducibility
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

private theorem matrixUnitAverage_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖matrixUnitAverage E x‖ ≤ ‖x‖ := by
  apply norm_finiteAverage_le
  intro g
  exact (norm_unitaryConj (matrixUnitSignedRepresentation E g) x).le

private theorem matrixUnitAverage_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : VonNeumannAlgebra H) (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra) {x : H →L[ℂ] H} (hx : x ∈ M) :
    matrixUnitAverage E x ∈ M := by
  change (Fintype.card (SignedPermutation ι) : ℂ)⁻¹ •
    ∑ g : SignedPermutation ι,
      ((matrixUnitSignedRepresentation E g : H →L[ℂ] H) * x *
        star (matrixUnitSignedRepresentation E g : H →L[ℂ] H)) ∈ M
  apply M.toStarSubalgebra.smul_mem
  apply M.toStarSubalgebra.sum_mem
  intro g _
  exact M.mul_mem (M.mul_mem (hEM (matrixUnitSignedRepresentation_mem E g)) hx)
    (M.toStarSubalgebra.star_mem' (hEM (matrixUnitSignedRepresentation_mem E g)))

private theorem matrixUnitAverage_sub_fixed_norm_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (x p : H →L[ℂ] H)
    (hp : ∀ a ∈ E.algebra, a * p = p * a) :
    ‖matrixUnitAverage E x - p‖ ≤ ‖x - p‖ := by
  have he : matrixUnitAverage E x - p = finiteAverage
      (fun g : SignedPermutation ι =>
        unitaryConj (matrixUnitSignedRepresentation E g) x - p) := by
    rw [finiteAverage_sub, finiteAverage_const]
    rfl
  rw [he]
  apply norm_finiteAverage_le
  intro g
  have hfix : unitaryConj (matrixUnitSignedRepresentation E g) p = p :=
    (commute_unitary_iff_star_right_conjugate
      (matrixUnitSignedRepresentation E g).property).mp
      (hp _ (matrixUnitSignedRepresentation_mem E g))
  calc
    _ = ‖unitaryConj (matrixUnitSignedRepresentation E g) (x - p)‖ := by
      rw [unitaryConj_sub, hfix]
    _ ≤ ‖x - p‖ := (norm_unitaryConj (matrixUnitSignedRepresentation E g) (x - p)).le

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

/-- Concrete matrix-stage averages provide a scalar near every ambient
operator which commutes with those stages. -/
theorem exists_scalar_near_of_increasing_matrix_averages
    (M : VonNeumannAlgebra H)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (x p : H →L[ℂ] H) (hx : x ∈ M)
    (hp : ∀ n a, a ∈ (E n).algebra → a * p = p * a) :
    ∃ z : ℂ, ‖z • (1 : H →L[ℂ] H) - p‖ ≤ ‖x - p‖ := by
  let f : ℕ → H →L[ℂ] H := fun n => matrixUnitAverage (E n) x
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨T, _, hlim⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω f ‖x‖
    (norm_nonneg x) (fun n => matrixUnitAverage_norm_le (E n) x)
  have hTM : T ∈ M := Generator.Tracial.weak_operator_limit_mem M
    (fun n => ⟨f n, matrixUnitAverage_mem M (E n) (hEM n) hx⟩) T hlim
  obtain ⟨z, hz⟩ := hirr T hTM
    (matrixUnitAverage_weak_limit_commutes d E hmono x T hω hlim)
  refine ⟨z, ?_⟩
  rw [← hz]
  apply norm_le_of_weak_limit (l := (ω : Filter ℕ)) (fun n => f n - p) (T - p)
    (norm_nonneg (x - p)) (fun n => matrixUnitAverage_sub_fixed_norm_le (E n) x p (hp n))
  intro ξ η
  simpa only [sub_apply, inner_sub_right] using
    (hlim ξ η).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => inner ℂ η (p ξ)) (ω : Filter ℕ) (𝓝 (inner ℂ η (p ξ))))

/-- The neighbor has no nontrivial projections in the relative commutant
when the ordinary gap is below one half. -/
theorem relative_projection_trivial_of_increasing_matrix_averages
    (M N : VonNeumannAlgebra H)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (p : Algebra N) (hp : IsStarProjection p)
    (hcomm : ∀ n a, a ∈ (E n).algebra → a * p.val = p.val * a) :
    p = 0 ∨ p = 1 := by
  have hpp : IsStarProjection p.val := hp.map N.toStarSubalgebra.subtype
  obtain ⟨x, hx, hxp⟩ := exists_unitBall_approx (M := N) (N := M)
    ⟨p.property, hpp.norm_le⟩ (by simpa only [kkDistance_comm] using hgap)
  obtain ⟨z, hz⟩ := exists_scalar_near_of_increasing_matrix_averages M d E hmono hEM hirr
    x p.val hx.1 hcomm
  have hr : ‖x - p.val‖ < 1 / 2 := by simpa only [norm_sub_rev] using hxp
  exact (projection_eq_zero_or_one_of_near_scalar p.val hpp z (hz.trans_lt hr)).imp
    (fun h => Subtype.ext h) (fun h => Subtype.ext h)

/-- Commutation with all matrix stages extends to their generated von
Neumann algebra. -/
theorem commute_generated_of_commute_matrix_stages
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hT : ∀ n a, a ∈ (E n).algebra → a * T = T * a) :
    ∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a := by
  let C := StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
  have hEC : ∀ n, (E n).algebra ≤ C := by
    intro n a ha
    change a ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
    rw [StarSubalgebra.mem_centralizer_iff]
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    refine ⟨(hT n a ha).symm, ?_⟩
    have he := congrArg star (hT n (star a) ((E n).algebra.star_mem' ha))
    simpa only [star_mul, star_star] using he
  let A : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n, (E n).algebra
  have hi : A ≤ C := iSup_le hEC
  have hc : T ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    intro a ha
    have hh := hi ha
    change a ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) at hh
    rw [StarSubalgebra.mem_centralizer_iff] at hh
    exact (hh T (Set.mem_singleton T)).1.symm
  intro a ha
  change a ∈ (generatedVonNeumannAlgebra (⨆ n, (E n).algebra) :
    Set (H →L[ℂ] H)) at ha
  rw [generatedVonNeumannAlgebra_coe] at ha
  exact (ha T hc).symm

/-- Relative irreducibility in the first algebra passes to the neighbor
for the actual weakly generated common increasing matrix algebra. -/
theorem relative_irreducibility_of_near_increasing_matrices_oai
    (M N : VonNeumannAlgebra H)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M,
      (∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2) :
    ∀ T ∈ N,
      (∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  let R := generatedVonNeumannAlgebra (⨆ n, (E n).algebra)
  let P := vonNeumannIntersection N R.commutant
  have hstage (n : ℕ) {a : H →L[ℂ] H} (ha : a ∈ (E n).algebra) : a ∈ R :=
    subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n) ha)
  have hproj (q : Algebra P) (hq : IsStarProjection q) : q = 0 ∨ q = 1 := by
    let qN : Algebra N := ⟨q.val, q.property.1⟩
    have hqN : IsStarProjection qN := hq.map
      (StarSubalgebra.inclusion (show P.toStarSubalgebra ≤ N.toStarSubalgebra from fun _ hx => hx.1))
    have hcomm : ∀ n a, a ∈ (E n).algebra → a * qN.val = qN.val * a := by
      intro n a ha
      exact VonNeumannAlgebra.mem_commutant_iff.mp q.property.2 a (hstage n ha)
    have hm := relative_projection_trivial_of_increasing_matrix_averages M N d E hmono hEM
      (fun T hTM hTc => hirr T hTM (commute_generated_of_commute_matrix_stages d E T hTc))
      hgap qN hqN hcomm
    rcases hm with h | h
    · left
      apply Subtype.ext
      change qN.val = 0
      exact congrArg Subtype.val h
    · right
      apply Subtype.ext
      change qN.val = 1
      exact congrArg Subtype.val h
  intro T hTN hTR
  let a : Algebra P := ⟨T, hTN, VonNeumannAlgebra.mem_commutant_iff.mpr hTR⟩
  let p : Generator.Tracial.AlgebraProjection P := ⟨1, IsStarProjection.one _⟩
  have hmin : ∀ q : Generator.Tracial.AlgebraProjection P, q ≤ p → q.val = 0 ∨ q.val = p.val := by
    intro q _
    exact hproj q.val q.property
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p hmin a
    (by change 1 * a = a; exact one_mul a) (by change a * 1 = a; exact mul_one a)
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.relative_irreducibility_of_near_increasing_matrices_oai.{u_1} := @OAI.KadisonKastler.relative_irreducibility_of_near_increasing_matrices_oai.{u_1}
