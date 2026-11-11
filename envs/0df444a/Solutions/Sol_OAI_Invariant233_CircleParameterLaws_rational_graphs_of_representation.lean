-- Prove2me | solution 1 for OAI.Invariant233.CircleParameterLaws.rational_graphs_of_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:41.887169+00:00
-- url     : https://prove2.me/submissions/cd514c48-b97c-4483-9a15-0400b07cd257

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR000
import Definitions.Def_Q234IR001
import Theorems.Thm_OAI_Invariant233_CircleParameterLaws_exists_rational_graph_field

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRationalGraphFields
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.CircleParameterData

theorem rationalGraphIdentities_congr_ae (p : CircleParameterData) (θ : ℝ)
    {P Q : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ}
    (hPQ : P =ᵐ[circleMeasure] Q) :
    p.RationalGraphIdentities θ P ↔ p.RationalGraphIdentities θ Q := by
  have htrans : ∀ᵐ x ∂circleMeasure, ∀ (A : ℕ) (r : ℤ),
      P (x + p.rationalTranslation A r) = Q (x + p.rationalTranslation A r) := by
    apply ae_all_iff.mpr
    intro A
    apply ae_all_iff.mpr
    intro r
    have hmp : MeasurePreserving (fun x : Circle => x + p.rationalTranslation A r)
        circleMeasure circleMeasure := by
      change MeasurePreserving _ volume volume
      exact measurePreserving_add_right volume _
    exact hmp.quasiMeasurePreserving.ae (p := fun x => P x = Q x) hPQ
  constructor
  · intro h
    filter_upwards [h, hPQ, htrans] with x hx he hs
    intro A hA r
    rw [← he, ← hs A r]
    exact hx A hA r
  · intro h
    filter_upwards [h, hPQ, htrans] with x hx he hs
    intro A hA r
    rw [he, hs A r]
    exact hx A hA r

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RationalGraphs
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem rational_graphs_of_representation_oai
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    p.RationalGraphIdentities θ F := by
  obtain ⟨G, _, _, _, hGrep, hG⟩ := hp.exists_rational_graph_field hmem hP hT
  have heq : G =ᵐ[circleMeasure] F :=
    L2Multiplication.field_unique_of_representation
      (default : HilbertBasis ℤ ℂ Rotation.Fiber) P G F hGrep hrep
  exact (p.rationalGraphIdentities_congr_ae θ heq).mp hG

end Invariant233.CircleParameterLaws

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleParameterLaws.rational_graphs_of_representation_oai := @OAI.Invariant233.CircleParameterLaws.rational_graphs_of_representation_oai
