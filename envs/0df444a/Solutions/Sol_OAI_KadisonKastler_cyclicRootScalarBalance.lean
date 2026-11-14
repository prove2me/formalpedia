-- Prove2me | solution 1 for OAI.KadisonKastler.cyclicRootScalarBalance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:14:22.061656+00:00
-- url     : https://prove2.me/submissions/0491f5b8-df72-40f5-b53a-093fa3b1c126

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.LinearAlgebra.Countable
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
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
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
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
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
import Definitions.Def_Q260K045

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceFrequencyVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded-frequency vector for the core trace

The scalar weight is exp(pi (s-1)) on (0,1], in the Fourier convention
exp(-2 pi i t s). The corresponding vector has explicit L2 bounds and frequency support.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

theorem coreTraceFrequencyScalar_apply_ae :
    coreTraceFrequencyScalar =ᵐ[volume] coreTraceFrequencyFunction :=
  coreTraceFrequencyFunction_memLp.coeFn_toLp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceWeightShift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Translation covariance of the clipped exponential trace weight -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem coreTraceFrequencyFunction_shift (a t : ℝ) :
    (Set.Ioc (0 : ℝ) 1).indicator (fun s => coreTraceFrequencyFunction (s + a)) t =
      (Real.exp (Real.pi * a) : ℂ) *
        (Set.Ioc (-a) (1 - a)).indicator coreTraceFrequencyFunction t := by
  have hmem : t ∈ Set.Ioc (-a) (1 - a) ↔ t + a ∈ Set.Ioc (0 : ℝ) 1 := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
    by_cases ha : t + a ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem (hmem.mpr ha)]
      simp only [coreTraceFrequencyFunction, Set.indicator_of_mem ht,
        Set.indicator_of_mem ha, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem (mt hmem.mp ha)]
      simp [coreTraceFrequencyFunction, ha]
  · rw [Set.indicator_of_notMem ht]
    by_cases ha : t ∈ Set.Ioc (-a) (1 - a) <;>
      simp [coreTraceFrequencyFunction, ht, ha]

theorem coreTraceFrequencyScalar_shift (a : ℝ) :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
      (regularTranslateApply a coreTraceFrequencyScalar) =
      (Real.exp (Real.pi * a) : ℂ) •
        regularIndicatorProjection (Set.Ioc (-a) (1 - a)) measurableSet_Ioc
          coreTraceFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc (regularTranslateApply a coreTraceFrequencyScalar),
    regularTranslateApply_ae a coreTraceFrequencyScalar,
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      coreTraceFrequencyScalar_apply_ae,
    regularIndicatorProjection_apply_ae (Set.Ioc (-a) (1 - a)) measurableSet_Ioc
      coreTraceFrequencyScalar,
    coreTraceFrequencyScalar_apply_ae,
    Lp.coeFn_smul (Real.exp (Real.pi * a) : ℂ)
      (regularIndicatorProjection (Set.Ioc (-a) (1 - a)) measurableSet_Ioc
        coreTraceFrequencyScalar)] with t hp ht hw hq hv hs
  simp only [Function.comp_def] at hw
  rw [hp, hs, Pi.smul_apply, hq]
  by_cases hti : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hti, ht, hw]
    by_cases hta : t ∈ Set.Ioc (-a) (1 - a)
    · rw [Set.indicator_of_mem hta, hv]
      simpa only [Set.indicator_of_mem hti, Set.indicator_of_mem hta, smul_eq_mul] using
        coreTraceFrequencyFunction_shift a t
    · rw [Set.indicator_of_notMem hta]
      simpa only [Set.indicator_of_mem hti, Set.indicator_of_notMem hta, mul_zero,
        smul_zero] using coreTraceFrequencyFunction_shift a t
  · rw [Set.indicator_of_notMem hti]
    by_cases hta : t ∈ Set.Ioc (-a) (1 - a)
    · rw [Set.indicator_of_mem hta, hv]
      simp [coreTraceFrequencyFunction, hti]
    · rw [Set.indicator_of_notMem hta, smul_zero]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceSpectralBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Balance of the two Tomita weights under the core frequency shift -/

namespace KadisonKastler

noncomputable section

theorem coreTrace_exp_sqrt_balance {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Real.exp (Real.pi * (resolventLogFrequency s / (2 * Real.pi))) * Real.sqrt s =
      Real.sqrt (1 - s) := by
  have hπ : Real.pi * (resolventLogFrequency s / (2 * Real.pi)) =
      resolventLogFrequency s / 2 := by field_simp
  rw [hπ]
  have he : Real.exp (resolventLogFrequency s / 2) ^ 2 =
      Real.exp (resolventLogFrequency s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (resolventLogFrequency s) * s = 1 - s := by
    rw [resolventLogFrequency, Real.exp_sub, Real.exp_log (sub_pos.mpr hs1), Real.exp_log hs]
    field_simp
  have hsq : (Real.exp (resolventLogFrequency s / 2) * Real.sqrt s) ^ 2 =
      (Real.sqrt (1 - s)) ^ 2 := by
    rw [mul_pow, he, Real.sq_sqrt hs.le, hr, Real.sq_sqrt (sub_pos.mpr hs1).le]
  exact (sq_eq_sq₀ (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg s))
    (Real.sqrt_nonneg (1 - s))).mp hsq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceScalarBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The trace balance on scalar L2 frequency packets -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem unitWindow_translate_conjugate (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    regularTranslateApply a
      (regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (-a) f)) =
      regularIndicatorProjection (Set.Ioc (-a) (1-a)) measurableSet_Ioc f := by
  have hmem (t : ℝ) : t + a ∈ Set.Ioc (0 : ℝ) 1 ↔ t ∈ Set.Ioc (-a) (1-a) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae a
      (regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (-a) f)),
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (regularIndicatorProjection_apply_ae (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (-a) f)),
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (regularTranslateApply_ae (-a) f),
    regularIndicatorProjection_apply_ae (Set.Ioc (-a) (1-a)) measurableSet_Ioc f]
    with t ht hp hf hq
  simp only [Function.comp_def] at hp hf
  rw [ht, hp, hq]
  by_cases h : t ∈ Set.Ioc (-a) (1-a)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem t).mpr h), hf]
    congr 1
    ring
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt (hmem t).mp h)]

theorem coreTraceFrequencyScalar_spectral_balance
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (Real.sqrt s : ℂ) •
      regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
        (regularTranslateApply (resolventLogFrequency s / (2 * Real.pi))
          coreTraceFrequencyScalar) =
    (Real.sqrt (1-s) : ℂ) •
      regularTranslateApply (resolventLogFrequency s / (2 * Real.pi))
        (regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
          (regularTranslateApply (-(resolventLogFrequency s / (2 * Real.pi)))
            coreTraceFrequencyScalar)) := by
  rw [unitWindow_translate_conjugate, coreTraceFrequencyScalar_shift, smul_smul]
  congr 1
  rw [mul_comm]
  exact_mod_cast coreTrace_exp_sqrt_balance hs hs1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceScalarGauge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Trace balance between the two scalar gauge actions -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_frequencyWindow (a b : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularFrequencyWindow a b f) : RegularCoreHilbert H) =
      regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc (𝓕 f) := by
  unfold regularFrequencyWindow
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  exact (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _

theorem fourier_character_apply (l : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 ((regularCharacterUnitary (H := H) l :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) : RegularCoreHilbert H) =
      regularTranslateApply (-(l / (2 * Real.pi))) (𝓕 f) := by
  rw [regularCharacter_apply_eq_fourier_translate]
  exact (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _

theorem fourier_character_star_apply (l : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 ((star (regularCharacterUnitary (H := H) l) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) : RegularCoreHilbert H) =
      regularTranslateApply (l / (2 * Real.pi)) (𝓕 f) := by
  have he : (star (regularCharacterUnitary (H := H) l) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (-l) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    congrArg Subtype.val (regularGroup_star_eq (regularCharacterRepresentation (H := H)) l)
  rw [he, fourier_character_apply]
  simp only [neg_div, neg_neg]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem coreTrace_scalarGauge_balance {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (Real.sqrt s : ℂ) •
      regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
          ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar)) =
    (Real.sqrt (1-s) : ℂ) •
      (star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (resolventLogFrequency s) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
            ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar))) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  simp only [map_smul]
  change (Real.sqrt s : ℂ) • (𝓕 (_ : RegularCoreHilbert ℂ)) =
    (Real.sqrt (1-s) : ℂ) • (𝓕 (_ : RegularCoreHilbert ℂ))
  have hf : (𝓕 ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar) :
      RegularCoreHilbert ℂ) = coreTraceFrequencyScalar :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
  rw [fourier_frequencyWindow, fourier_character_star_apply, hf,
    fourier_character_star_apply, fourier_frequencyWindow, fourier_character_apply, hf]
  exact coreTraceFrequencyScalar_spectral_balance hs hs1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicSqrtGaugeBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two square-root spectral weights in a cyclic gauge model -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

omit [TopologicalSpace.SeparableSpace H] in
include hsep hcyc in
theorem cyclicRootScalarBalance_oai :
    let μ := modularCyclicMeasure (M := M) J Ω x
    let f := (Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar
    ∀ᵐ s ∂μ,
      cyclicLeftRootVector (M := M) J Ω x s • regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s.val)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      cyclicRightRootVector (M := M) J Ω x s •
        (star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s.val)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (resolventLogFrequency s.val) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f)) := by
  let μ := modularCyclicMeasure (M := M) J Ω x
  filter_upwards [graphResolventVectorMeasure_interior J Ω hsep hcyc x,
    ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)
      (resolventSqrtFunction (graphResolvent M J Ω 1)),
    ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)
      (resolventComplementSqrtFunction (graphResolvent M J Ω 1))]
    with s hs hv hw
  change cyclicLeftRootVector (M := M) J Ω x s = _ at hv
  change cyclicRightRootVector (M := M) J Ω x s = _ at hw
  rw [hv, hw]
  exact coreTrace_scalarGauge_balance hs.1 hs.2

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.cyclicRootScalarBalance_oai.{u_1} := @OAI.KadisonKastler.cyclicRootScalarBalance_oai.{u_1}
