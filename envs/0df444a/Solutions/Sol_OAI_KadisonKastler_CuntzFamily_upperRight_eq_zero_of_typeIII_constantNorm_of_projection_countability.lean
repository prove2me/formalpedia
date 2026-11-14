-- Prove2me | solution 1 for OAI.KadisonKastler.CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:21:20.439206+00:00
-- url     : https://prove2.me/submissions/dd8afba9-06cb-4255-b7a6-74915c139837

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
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
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
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
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
import Definitions.Def_Q260K033
import Theorems.Thm_OAI_KadisonKastler_CuntzFamily_exists_diagonal_average_mem
import Theorems.Thm_OAI_KadisonKastler_CuntzFamily_small_contraction_corner_mem
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_small_positive_product_of_projection_countability
import Theorems.Thm_OAI_KadisonKastler_norm_two_corner_diagonal_lt

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveCornerSquare
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A strictly positive off-diagonal matrix corner

A positive lower bound on the off-diagonal entry gives the two quadratic
corner bounds used by the strict diagonal-contraction estimate.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem scalar_sq_le_star_mul_of_scalar_le (a : A) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : algebraMap ℝ A δ ≤ a) : algebraMap ℝ A (δ ^ 2) ≤ star a * a := by
  have hd : 0 ≤ algebraMap ℝ A δ := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_nonneg hδ (zero_le_one : (0 : A) ≤ 1)
  have ha0 : 0 ≤ a := hd.trans ha
  have hsa := ha0.isSelfAdjoint
  have hs := (algebraMap_le_iff_le_spectrum hsa).mp ha
  have hsq := algebraMap_le_cfc (fun x : ℝ => x ^ 2) (δ ^ 2) a
    (fun x hx => pow_le_pow_left₀ hδ (hs x hx) 2) (ha := hsa)
  rw [cfc_pow_id (R := ℝ) a 2 hsa] at hsq
  simpa only [pow_two, hsa.star_eq] using hsq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixStrictContraction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pairedRepresentation_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strict diagonal contraction in two-by-two coordinates -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem firstBlockProjection_isStarProjection :
    IsStarProjection (firstBlockProjection (A := A)) := by
  constructor
  · ext i j
    simp only [firstBlockProjection, CStarMatrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, diagonalStarAlgHom_apply]
  · ext i j
    simp only [firstBlockProjection, CStarMatrix.star_apply]
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, diagonalStarAlgHom_apply]

theorem secondBlockProjection_eq :
    1 - firstBlockProjection (A := A) = blockDiagonal 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

theorem lowerLeft_column_square (T : CStarMatrix (Fin 2) (Fin 2) A) :
    star ((1 - firstBlockProjection) * (T * firstBlockProjection)) *
        ((1 - firstBlockProjection) * (T * firstBlockProjection)) =
      blockDiagonal (star (T 1 0) * T 1 0) 0 := by
  rw [secondBlockProjection_eq]
  ext i j
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

theorem upperRight_column_square (T : CStarMatrix (Fin 2) (Fin 2) A) :
    star (firstBlockProjection * (T * (1 - firstBlockProjection))) *
        (firstBlockProjection * (T * (1 - firstBlockProjection))) =
      blockDiagonal 0 (star (T 0 1) * T 0 1) := by
  rw [secondBlockProjection_eq]
  ext i j
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

theorem two_corner_diagonal_eq (T : CStarMatrix (Fin 2) (Fin 2) A) :
    firstBlockProjection * T * firstBlockProjection +
      (1 - firstBlockProjection) * T * (1 - firstBlockProjection) =
      blockDiagonal (T 0 0) (T 1 1) := by
  rw [secondBlockProjection_eq]
  ext i j
  simp only [CStarMatrix.add_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

variable [PartialOrder A] [StarOrderedRing A]

attribute [local instance] OAI.KadisonKastler.matrixStrictContractionInstance1
attribute [local instance] OAI.KadisonKastler.matrixStrictContractionInstance2
attribute [local instance] OAI.KadisonKastler.matrixStrictContractionInstance3
local instance matrixStrictContractionInstance4 : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrderedRing _

theorem blockDiagonal_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ blockDiagonal a b := by
  have he : blockDiagonal a b = star (blockDiagonal (CFC.sqrt a) (CFC.sqrt b)) *
      blockDiagonal (CFC.sqrt a) (CFC.sqrt b) := by
    ext i j
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [blockDiagonal, diagonalStarAlgHom_apply, (CFC.sqrt_nonneg a).star_eq,
        (CFC.sqrt_nonneg b).star_eq, CFC.sqrt_mul_sqrt_self a ha,
        CFC.sqrt_mul_sqrt_self b hb]
  rw [he]
  exact star_mul_self_nonneg _

theorem blockDiagonal_mono {a b c d : A} (hac : a ≤ c) (hbd : b ≤ d) :
    blockDiagonal a b ≤ blockDiagonal c d := by
  have he : blockDiagonal c d - blockDiagonal a b = blockDiagonal (c - a) (d - b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, diagonalStarAlgHom_apply]
  rw [← sub_nonneg, he]
  exact blockDiagonal_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hbd)

theorem norm_matrix_diagonal_lt_of_positive_corner [Nontrivial A]
    (T : CStarMatrix (Fin 2) (Fin 2) A) (hT : IsSelfAdjoint T)
    (δ : ℝ) (hδ : 0 < δ) (hc : algebraMap ℝ A δ ≤ T 0 1) :
    ‖blockDiagonal (T 0 0) (T 1 1)‖ < ‖T‖ := by
  have hd : 0 ≤ algebraMap ℝ A δ := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_nonneg hδ.le (zero_le_one : (0 : A) ≤ 1)
  have hsa : IsSelfAdjoint (T 0 1) := (hd.trans hc).isSelfAdjoint
  have hentry : T 1 0 = T 0 1 := by
    have he := congrArg (fun X : CStarMatrix (Fin 2) (Fin 2) A => X 1 0) hT.star_eq
    exact he.symm.trans hsa.star_eq
  have hsq := scalar_sq_le_star_mul_of_scalar_le (T 0 1) δ hδ.le hc
  have hδnorm : δ ≤ ‖T‖ := by
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hc hd
    have he : ‖algebraMap ℝ A δ‖ = δ := by
      rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos hδ]
    rw [he] at hn
    exact hn.trans (CStarMatrix.norm_entry_le_norm (M := T) (i := 0) (j := 1))
  have hpq : δ ^ 2 • firstBlockProjection (A := A) ≤
      star ((1 - firstBlockProjection) * (T * firstBlockProjection)) *
        ((1 - firstBlockProjection) * (T * firstBlockProjection)) := by
    rw [lowerLeft_column_square, hentry]
    convert blockDiagonal_mono hsq (le_refl (0 : A)) using 1
    all_goals try with_reducible_and_instances rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply,
        Algebra.algebraMap_eq_smul_one]
  have hqp : δ ^ 2 • (1 - firstBlockProjection (A := A)) ≤
      star (firstBlockProjection * (T * (1 - firstBlockProjection))) *
        (firstBlockProjection * (T * (1 - firstBlockProjection))) := by
    rw [upperRight_column_square, secondBlockProjection_eq]
    convert blockDiagonal_mono (le_refl (0 : A)) hsq using 1
    all_goals try with_reducible_and_instances rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockDiagonal, diagonalStarAlgHom_apply, Algebra.algebraMap_eq_smul_one]
  have hh := norm_two_corner_diagonal_lt firstBlockProjection T
    firstBlockProjection_isStarProjection hT δ hδ hδnorm hpq hqp
  rwa [two_corner_diagonal_eq] at hh

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIConstantNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Type III corners of a constant-norm convex family vanish

The nonzero corner can be made strictly positive by independent small
left and right contractions. Both contractions come from convex unitary
averages. Removing the resulting off-diagonal corner then contradicts
the constant norm of the family.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.typeIIIConstantNormInstance1
local instance typeIIIConstantNormInstance2 : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
local instance typeIIIConstantNormInstance3_r878fdb_1 (N : VonNeumannAlgebra H) : LE (Algebra N) :=
  (CStarAlgebra.spectralOrder (Algebra N)).toLE
attribute [local instance] OAI.KadisonKastler.typeIIIConstantNormInstance4
local instance typeIIIConstantNormInstance5_r878fdb_1 (N : VonNeumannAlgebra H) : Preorder (Algebra N) :=
  (CStarAlgebra.spectralOrder (Algebra N)).toPreorder
local instance typeIIIConstantNormInstance6 (N : VonNeumannAlgebra H) : StarOrderedRing (Algebra N) :=
  CStarAlgebra.spectralOrderedRing _

theorem CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability_oai
    (S : CuntzFamily (Fin 2) H) (N : VonNeumannAlgebra H) (hN : TypeIIIFactor N)
    (hFamilies : HasCountableProjectionFamilies N)
    (hS : ∀ i, S.entry i ∈ N) (K : Set (H →L[ℂ] H)) (hK : Convex ℝ K)
    (hinv : ∀ w : unitary (Algebra N), ∀ T ∈ K,
      unitaryConj (ambientAlgebraUnitary w) T ∈ K)
    (hself : ∀ T ∈ K, IsSelfAdjoint T) (r : ℝ) (hnorm : ∀ T ∈ K, ‖T‖ = r)
    (T : H →L[ℂ] H) (hT : T ∈ K) (hc : S.matrix T 0 1 ∈ N) :
    S.matrix T 0 1 = 0 := by
  let : Nontrivial (H →L[ℂ] H) := ⟨⟨1, 0, hN.nonzero⟩⟩
  by_contra hc0
  let c : Algebra N := ⟨S.matrix T 0 1, hc⟩
  have hcne : c ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  obtain ⟨a, b, ha, hb, δ, hδ, hpos⟩ :=
    hN.exists_small_positive_product_of_projection_countability hFamilies c hcne
  obtain ⟨V, hV, hVcorner⟩ := S.small_contraction_corner_mem N hS K hK hinv T hT a b ha hb
  have hpositive : algebraMap ℝ (H →L[ℂ] H) δ ≤ S.matrix V 0 1 := by
    have hm := (NonUnitalStarAlgHom.map_le_map_iff
      N.toStarSubalgebra.subtype.toNonUnitalStarAlgHom Subtype.val_injective).mpr hpos
    change δ • (1 : H →L[ℂ] H) ≤ a.val * c.val * b.val at hm
    rw [Algebra.algebraMap_eq_smul_one, hVcorner]
    exact hm
  have hmatrix : IsSelfAdjoint (S.matrix V) := by
    change star (S.matrixHom V) = S.matrixHom V
    rw [← map_star, (hself V hV).star_eq]
  have hlt := norm_matrix_diagonal_lt_of_positive_corner (S.matrix V) hmatrix δ hδ hpositive
  obtain ⟨W, hW, hWmatrix⟩ := S.exists_diagonal_average_mem N hS K hK hinv V hV
  rw [← hWmatrix, S.norm_matrix, S.norm_matrix, hnorm W hW, hnorm V hV] at hlt
  exact (lt_irrefl r) hlt

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability_oai.{u_1} := @OAI.KadisonKastler.CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability_oai.{u_1}
