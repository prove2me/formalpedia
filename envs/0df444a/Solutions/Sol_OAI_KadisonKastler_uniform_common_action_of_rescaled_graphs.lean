-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_common_action_of_rescaled_graphs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:19:14.214671+00:00
-- url     : https://prove2.me/submissions/771165dd-bf5f-4c2a-bf58-5249c2a8dc02

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
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
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K068
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_uniform_common_action_of_frequency_defects

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded resolvent estimate for separated spectral cuts

The estimate uses a right inverse only on one spectral subspace. All
operators in the proof are bounded; the later spectral representation
provides these identities for the resolvents of the modular operators.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem norm_separated_cuts_le
    (A B P Q R : H →L[ℂ] H) {e b r : ℝ}
    (he : 0 ≤ e) (hb : 0 ≤ b) (_hr : 0 ≤ r)
    (hcontract : b * r < 1)
    (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ r)
    (hQB : ‖Q * B‖ ≤ b) (hAB : ‖A - B‖ ≤ e)
    (hAR : A * R = P) (hPR : P * R = R) (hQBQ : Q * B * Q = Q * B) :
    ‖Q * P‖ ≤ e * r / (1 - b * r) := by
  have hid : Q * P = Q * (A - B) * R + (Q * B) * (Q * P) * R := by
    calc
      Q * P = Q * (A * R) := by rw [hAR]
      _ = Q * (A - B) * R + Q * B * R := by noncomm_ring
      _ = Q * (A - B) * R + (Q * B) * (Q * P) * R := by
        rw [← mul_assoc (Q * B) Q P, hQBQ, mul_assoc (Q * B) P R, hPR]
  have hfirst : ‖Q * (A - B) * R‖ ≤ e * r := calc
    _ ≤ (‖Q‖ * ‖A - B‖) * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * e) * r := mul_le_mul
      (mul_le_mul hQ hAB (norm_nonneg _) (by norm_num)) hR (norm_nonneg _) (by positivity)
    _ = e * r := by rw [one_mul]
  have hsecond : ‖(Q * B) * (Q * P) * R‖ ≤ b * ‖Q * P‖ * r := calc
    _ ≤ (‖Q * B‖ * ‖Q * P‖) * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (b * ‖Q * P‖) * r := mul_le_mul
      (mul_le_mul_of_nonneg_right hQB (norm_nonneg _)) hR (norm_nonneg _) (by positivity)
  have hn : ‖Q * P‖ ≤ e * r + b * ‖Q * P‖ * r := by
    conv_lhs => rw [hid]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  apply (le_div_iff₀ (by linarith : 0 < 1 - b * r)).mpr
  nlinarith

/-- A convenient uniform constant for the resolvent cuts separated by
one unit of logarithmic spectrum. -/
theorem norm_logarithmically_separated_cuts_le
    (A B P Q R : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hQ : ‖Q‖ ≤ 1)
    (hR : ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)))
    (hQB : ‖Q * B‖ ≤ Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))))
    (hAB : ‖A - B‖ ≤ e)
    (hAR : A * R = P) (hPR : P * R = R) (hQBQ : Q * B * Q = Q * B) :
    ‖Q * P‖ ≤ ((1 + Real.exp (-(1 / 2 : ℝ))) /
      (1 - Real.exp (-(1 / 2 : ℝ)))) * e := by
  let q := Real.exp (-(1 / 2 : ℝ))
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hc : (q / (1 + q)) * (1 + q) = q := div_mul_cancel₀ _ (by positivity)
  have h := norm_separated_cuts_le A B P Q R he (by positivity : 0 ≤ q / (1 + q))
    (by positivity : 0 ≤ 1 + q) (by rw [hc]; exact hq1) hQ hR hQB hAB hAR hPR hQBQ
  rw [hc] at h
  exact h.trans_eq (by dsimp [q] <;> ring)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphResolventCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive compression of the actual graph projection

The first diagonal entry is the bounded graph resolvent. Its comparison
follows directly from the norm comparison of the whole graph projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_graphResolvent_sub_le
    (P Q : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    ‖graphResolvent P J Ω c - graphResolvent Q J Ω c‖ ≤
      ‖rescaledGraphProjection P J Ω c - rescaledGraphProjection Q J Ω c‖ := by
  have he : graphResolvent P J Ω c - graphResolvent Q J Ω c =
      Generator.operatorEntry
        (rescaledGraphProjection P J Ω c - rescaledGraphProjection Q J Ω c) 0 0 := by
    ext x
    rfl
  rw [he]
  exact norm_graph_operatorEntry_le _ _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyPoissonProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Poisson products from the published Hardy evaluation

The boundary multiplication operators and their positive-frequency algebra
are concrete. Multiplicativity is obtained by applying the precisely cited
published evaluation homomorphism, including for constant middle factors.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.mul
    {B S : ℝ → H →L[ℂ] H}
    {T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : RepresentsOperatorField volume B T) (hS : RepresentsOperatorField volume S V) :
    RepresentsOperatorField volume (fun t => B t * S t) (T * V) := by
  intro f
  filter_upwards [hB (V f), hS f] with t h₁ h₂
  change (T (V f)) t = B t (S t (f t))
  rw [h₁, h₂]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSeparatedCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Separated modular cuts from the actual graph comparison -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cut comparison is proved from a one-algebra spectral resolution
and the independently proved two-algebra graph estimate. -/
theorem norm_modular_separated_cuts_le
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    (J : H ≃ₗᵢ⋆[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hgraph : ∀ c : ℝ, 0 < c →
      ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ e)
    (a : ℝ) :
    ‖(1 - n.upperCut (a - 1 / 2)) * m.upperCut (a + 1 / 2)‖ ≤
      ((1 + Real.exp (-(1 / 2 : ℝ))) / (1 - Real.exp (-(1 / 2 : ℝ)))) * e := by
  obtain ⟨R, hR, hAR, hPR⟩ := m.high_inverse J a
  apply norm_logarithmically_separated_cuts_le
    (1 - graphResolvent M J Ω (Real.exp (-a / 2)))
    (1 - graphResolvent N J Ω (Real.exp (-a / 2)))
    (m.upperCut (a + 1 / 2)) (1 - n.upperCut (a - 1 / 2)) R he
    (n.lower_contracts _) hR (n.low_bound J a) ?_ hAR hPR (n.low_support J a)
  have hid : (1 - graphResolvent M J Ω (Real.exp (-a / 2))) -
      (1 - graphResolvent N J Ω (Real.exp (-a / 2))) =
      -(graphResolvent M J Ω (Real.exp (-a / 2)) -
        graphResolvent N J Ω (Real.exp (-a / 2))) := by abel
  rw [hid, norm_neg]
  exact (norm_graphResolvent_sub_le M N J Ω _).trans (hgraph _ (Real.exp_pos _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularFrequencyBridge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From separated modular cuts to actual Fourier defects

The character moves the Fourier cut by one. Conjugating by the two
modular gauges then turns its off-diagonal block into multiplication by
the product of separated logarithmic spectral projections.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem field_norm_bound
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : RepresentsOperatorField volume F T) {e : ℝ} (he : 0 ≤ e)
    (hF : ∀ᵐ t, ‖F t‖ ≤ e) : ‖T‖ ≤ e := by
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hT f, hF] with t ht hnorm
  rw [ht]
  exact ((F t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

omit [CompleteSpace H] in
private theorem field_one_sub
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : RepresentsOperatorField volume F T) :
    RepresentsOperatorField volume (fun t => 1 - F t) (1 - T) := by
  intro f
  filter_upwards [hT f, Lp.coeFn_sub f (T f)] with t ht hs
  change (f - T f) t = (1 - F t) (f t)
  rw [hs]
  simp only [Pi.sub_apply, ht, sub_apply, one_apply_eq_self]

theorem norm_modular_gauge_cut_product_le
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    {e : ℝ} (he : 0 ≤ e)
    (hcuts : ∀ a, ‖(1 - n.upperCut (a - 1 / 2)) * m.upperCut (a + 1 / 2)‖ ≤ e)
    (a : ℝ) :
    ‖(1 - (star (regularGauge n.group n.continuous) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection (a - 1) *
        (regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
      ((star (regularGauge m.group m.continuous) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection a *
        (regularGauge m.group m.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))‖ ≤ e := by
  rw [m.gauge_identity a, n.gauge_identity (a - 1)]
  let E := (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
  let A := regularFieldOperator volume (fun ξ => n.upperCut (a - 1 - 2 * Real.pi * ξ))
    (n.measurable (a - 1)) 1 (Filter.Eventually.of_forall fun ξ => n.upper_contracts _)
  let B := regularFieldOperator volume (fun ξ => m.upperCut (a - 2 * Real.pi * ξ))
    (m.measurable a) 1 (Filter.Eventually.of_forall fun ξ => m.upper_contracts _)
  change ‖(1 - E A) * E B‖ ≤ e
  rw [← map_one E, ← map_sub E, ← map_mul E, StarAlgEquiv.norm_map]
  apply field_norm_bound
    ((field_one_sub (regularFieldOperator_represents volume _ _ _ _)).mul
      (regularFieldOperator_represents volume _ _ _ _)) he
  apply Filter.Eventually.of_forall
  intro ξ
  have h := hcuts (a - 1 / 2 - 2 * Real.pi * ξ)
  have hl : a - 1 / 2 - 2 * Real.pi * ξ - 1 / 2 = a - 1 - 2 * Real.pi * ξ := by ring
  have hh : a - 1 / 2 - 2 * Real.pi * ξ + 1 / 2 = a - 2 * Real.pi * ξ := by ring
  simpa only [hl, hh] using h

private theorem frequency_block_factorization
    (U V C : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (P Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hshift : (1 - P) * (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (1 - Q)) :
    (1 - P) * ((C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        (star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) * P =
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * V *
        ((1 - (star V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * Q * (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
          ((star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * P * (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))) *
        (star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hV := Unitary.mul_star_self_of_mem V.property
  have hU := Unitary.mul_star_self_of_mem U.property
  simp only [mul_assoc] at hshift ⊢
  rw [← mul_assoc (1 - P) (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H), hshift]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
  simp only [hU, one_mul, mul_one,
    ← mul_assoc (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (star V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H), hV]

theorem modular_comparison_multiplier
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    (hW : ∀ x, Continuous (fun t => (modularComparisonField m.group n.group t : H →L[ℂ] H) x)) :
    regularFieldOperator volume (modulatedUnitaryField (modularComparisonField m.group n.group))
      (fun x => (modulatedUnitaryField_continuous _ hW x).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one _)) =
    (regularCharacterUnitary (H := H) 1 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (star (regularGauge m.group m.continuous) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularFieldOperator_represents volume _ _ _ _ f,
    regularCharacterUnitary_apply_ae 1
      ((regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((star (regularGauge m.group m.continuous) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    regularGauge_apply_ae n.group n.continuous
      ((star (regularGauge m.group m.continuous) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_star_apply_ae m.group m.continuous f] with t h₁ h₂ h₃ h₄
  change _ = (regularCharacterUnitary (H := H) 1 :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    ((regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star (regularGauge m.group m.continuous) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t
  rw [h₁, h₂, h₃, h₄]
  simp only [modulatedUnitaryField, modularComparisonField, regularCharacterScalar,
    one_mul, smul_apply]
  rfl

theorem frequencyDefectBound_of_modular_cuts
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    (hW : ∀ x, Continuous (fun t => (modularComparisonField m.group n.group t : H →L[ℂ] H) x))
    {e : ℝ} (he : 0 ≤ e)
    (hcuts : ∀ a, ‖(1 - n.upperCut (a - 1 / 2)) * m.upperCut (a + 1 / 2)‖ ≤ e) :
    FrequencyDefectBound (modularComparisonField m.group n.group) hW e := by
  intro b
  rw [modular_comparison_multiplier m n hW]
  let a := -b
  let U := regularGauge m.group m.continuous
  let V := regularGauge n.group n.continuous
  let C := regularCharacterUnitary (H := H) 1
  change ‖(1 - regularFrequencyProjection a) *
    ((C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        (star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
      regularFrequencyProjection a‖ ≤ e
  have hshift : (1 - regularFrequencyProjection a) *
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        (1 - regularFrequencyProjection (a - 1)) := by
    have h := regularFrequencyProjection_character_intertwine (H := H) a (1 / (2 * Real.pi))
    have hc : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by
      field_simp [Real.pi_ne_zero]
    rw [hc] at h
    dsimp [C]
    simpa only [sub_mul, mul_sub, one_mul, mul_one] using congrArg
      (fun T => (regularCharacterUnitary (H := H) 1 :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) - T) h
  rw [frequency_block_factorization U V C _ _ hshift]
  simp only [← Unitary.coe_star]
  rw [CStarRing.norm_mul_coe_unitary, mul_assoc,
    CStarRing.norm_coe_unitary_mul, CStarRing.norm_coe_unitary_mul]
  exact norm_modular_gauge_cut_product_le m n he hcuts a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularGraphAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A common modular action from uniform rescaled graph comparison -/

namespace KadisonKastler

open MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem modularComparisonField_continuous
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω) (x : H) :
    Continuous (fun t => (modularComparisonField m.group n.group t : H →L[ℂ] H) x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs (y : H) : Continuous (fun s : ℝ =>
      (star (m.group (Multiplicative.ofAdd s)) : H →L[ℂ] H) y) := by
    simpa only [← Unitary.coe_star, regularGroup_star_eq, Function.comp_def] using
      (m.continuous y).comp continuous_neg
  exact tendsto_mul_contractions
    (fun s : ℝ => (n.group (Multiplicative.ofAdd s) : H →L[ℂ] H))
    (fun s : ℝ => (star (m.group (Multiplicative.ofAdd s)) : H →L[ℂ] H))
    (n.group (Multiplicative.ofAdd t) : H →L[ℂ] H)
    (star (m.group (Multiplicative.ofAdd t)) : H →L[ℂ] H)
    (fun s => norm_unitary_le_one _) (fun y => (n.continuous y).tendsto t)
    (fun y => (hs y).tendsto t) x

theorem modularComparisonField_star_continuous
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω) (x : H) :
    Continuous (fun t =>
      ((star (modularComparisonField m.group n.group t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) := by
  simpa only [modularComparisonField, star_mul, star_star] using
    modularComparisonField_continuous n m x

attribute [local instance] OAI.KadisonKastler.graphActionOrder
attribute [local instance] OAI.KadisonKastler.graphActionStarOrder
/-- The graph estimate now supplies both frequency defects. The uniform
tolerance and linear conjugacy constant precede all representation data. -/
theorem uniform_common_action_of_rescaled_graphs_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H)
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (hNest : PublishedRealNestDistance.{u})
    (hRealSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ γ0 K : ℝ, 0 < γ0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (Ω : H) (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
        (J : H ≃ₗᵢ⋆[ℂ] H),
      (∀ t, PublishedMultiplicationCorrection
        (unitaryConjugateAlgebra (modularComparisonField m.group n.group t) M)) →
      ∀ γ : ℝ, 0 < γ → γ < γ0 → kkDistance M N < γ →
      (∀ c : ℝ, 0 < c →
        ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ B * γ) →
      ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ K * γ ∧
        ∀ t, Conjugates (n.group t) (unitaryConjugateAlgebra q M)
          (unitaryConjugateAlgebra q M) := by
  let C := (1 + Real.exp (-(1 / 2 : ℝ))) / (1 - Real.exp (-(1 / 2 : ℝ)))
  have hC : 0 ≤ C := by
    have h : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by positivity) (by linarith)
  obtain ⟨γ0, K, hγ0, hK, h⟩ := uniform_common_action_of_frequency_defects
    hSpectral hCompare hSakai hDistance hHardy hNest hRealSpectral hDiagonal
    (mul_nonneg hC hB)
  refine ⟨γ0, K, hγ0, hK, ?_⟩
  intro H _ _ _ _ _ M N hM Ω m n J hCorrection γ hγ hsmall hgap hgraph
  have he : 0 ≤ B * γ := mul_nonneg hB hγ.le
  have hcuts := norm_modular_separated_cuts_le m n J he hgraph
  have hgraph' (c : ℝ) (hc : 0 < c) :
      ‖rescaledGraphProjection N J Ω c - rescaledGraphProjection M J Ω c‖ ≤ B * γ := by
    simpa only [norm_sub_rev] using hgraph c hc
  have hcuts' := norm_modular_separated_cuts_le n m J he hgraph'
  have hF := frequencyDefectBound_of_modular_cuts m n
    (modularComparisonField_continuous m n) (mul_nonneg hC he) hcuts
  have hG := frequencyDefectBound_of_modular_cuts n m
    (modularComparisonField_continuous n m) (mul_nonneg hC he) hcuts'
  rw [← mul_assoc] at hF hG
  apply h H M N hM m.group n.group m.normalizes n.normalizes
    (modularComparisonField_continuous m n) (modularComparisonField_star_continuous m n)
    hCorrection γ hγ hsmall hF ?_ hgap
  have hs : (fun t => star (modularComparisonField m.group n.group t)) =
      modularComparisonField n.group m.group := by
    funext t
    simp only [modularComparisonField, star_mul, star_star]
  simpa only [hs] using hG

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_common_action_of_rescaled_graphs_oai.{u} := @OAI.KadisonKastler.uniform_common_action_of_rescaled_graphs_oai.{u}
