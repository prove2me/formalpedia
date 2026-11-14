-- Prove2me | solution 1 for OAI.KadisonKastler.local_scaling_adjoint_commutator_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:53:46.460357+00:00
-- url     : https://prove2.me/submissions/7643db74-efb4-4727-b525-363400900683

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Definitions.Def_Q260K034

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongReferenceTests
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong convergence from the reference vector and its commutant orbit -/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem commutant_cyclic_of_separating_reference
    (ξ : H) (hsep : Function.Injective (algebraVectorMap M ξ)) :
    DenseRange (algebraVectorMap M.commutant ξ) := by
  let p := vectorSupportProjection M ξ
  have hp : p.val=1 := hsep (by
    change p.val.val ξ=(1 : H →L[ℂ] H) ξ
    exact vectorSupportProjection_apply M ξ)
  have he : (vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection=1 :=
    congrArg (fun a : Algebra M => a.val) hp
  intro η
  have hm := Submodule.starProjection_apply_mem
    (vectorOrbitClosure M.commutant.toStarSubalgebra ξ) η
  rw [he,one_apply_eq_self] at hm
  exact hm

theorem algebra_strong_tendsto_of_reference
    {ι : Type*} {l : Filter ι}
    (ξ : H) (hcyc : DenseRange (algebraVectorMap M.commutant ξ))
    (T : ι → Algebra M) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖T n‖ ≤ C)
    (hξ : Tendsto (fun n => (T n).val ξ) l (𝓝 0)) (η : H) :
    Tendsto (fun n => (T n).val η) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 2*(C+1) := by positivity
  obtain ⟨b,hb⟩ := hcyc.exists_dist_lt η (div_pos hε hden)
  have hnear : ‖η-b.val ξ‖ < ε/(2*(C+1)) := by
    change dist η (b.val ξ) < ε/(2*(C+1)) at hb
    simpa only [dist_eq_norm] using hb
  have hsmall : C*‖η-b.val ξ‖ < ε/2 := by
    have hmul := (lt_div_iff₀ hden).mp hnear
    nlinarith only [hmul,norm_nonneg (η-b.val ξ)]
  have hcomm (n : ι) : (T n).val (b.val ξ)=b.val ((T n).val ξ) :=
    congrArg (fun A : H →L[ℂ] H => A ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp b.property (T n).val (T n).property)
  have hbzero : Tendsto (fun n => (T n).val (b.val ξ)) l (𝓝 0) := by
    have h := b.val.continuous.tendsto (0 : H) |>.comp hξ
    simpa only [hcomm,map_zero,Function.comp_def] using h
  have hbNorm : Tendsto (fun n => ‖(T n).val (b.val ξ)‖) l (𝓝 0) := by
    simpa only [norm_zero] using hbzero.norm
  filter_upwards [hbNorm.eventually (gt_mem_nhds (half_pos hε))] with n hn
  have he : (T n).val η=(T n).val (η-b.val ξ)+(T n).val (b.val ξ) := by
    rw [← map_add,sub_add_cancel]
  have hbn : ‖(T n).val (η-b.val ξ)‖ ≤ C*‖η-b.val ξ‖ :=
    ((T n).val.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  have hnη : ‖(T n).val η‖ < ε := by
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith only [hbn,hsmall,hn])
  simpa only [dist_zero_right] using hnη

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalingCoisometryEstimates
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reference-state estimates for a scaling coisometry -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H} {r : ℝ}

theorem coisometry_norm_le (v : Algebra M) (hv : v*star v=1) : ‖v‖ ≤ 1 := by
  have hn : ‖v*star v‖=‖v‖*‖v‖ := CStarRing.norm_self_mul_star
  rw [hv] at hn
  have h1 : ‖(1 : Algebra M)‖ ≤ 1 := by
    have he : ‖star (1 : Algebra M)*(1 : Algebra M)‖=
        ‖(1 : Algebra M)‖*‖(1 : Algebra M)‖ := CStarRing.norm_star_mul_self
    simp only [star_one,one_mul] at he
    nlinarith [norm_nonneg (1 : Algebra M)]
  nlinarith [norm_nonneg v]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalingAdjointEstimate
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The adjoint reference estimate for scaling coisometries -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem centralizerProjection_right_norm_le (d : ModularConjugationData M Ω)
    (p : AlgebraProjection M) (hc : ProductStateCentralizes M Ω p.val.val)
    (a : Algebra M) : ‖a.val (p.val.val Ω)‖ ≤ ‖a.val Ω‖ := by
  let R := conjugationOperator d.conjugation p.val.val
  have hR : R ∈ M.commutant := d.right_mem (R := M) le_rfl p.val
  have hcomm : a.val*R=R*a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp hR a.val a.property
  have hfix : R Ω=p.val.val Ω := by
    have hh := d.centralizer_vector p.val (fun b => hc b.val b.property)
    have he : star p.val.val=p.val.val := congrArg (fun b : Algebra M => b.val)
      p.property.isSelfAdjoint.star_eq
    rwa [he] at hh
  have hnorm : ‖R‖ ≤ 1 := by
    rw [norm_conjugationOperator d.conjugation d.involutive]
    exact p.property.norm_le
  calc
    _ = ‖R (a.val Ω)‖ := by
      rw [← hfix]
      exact congrArg norm (congrArg (fun T : H →L[ℂ] H => T Ω) hcomm)
    _ ≤ ‖R‖*‖a.val Ω‖ := R.le_opNorm _
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hnorm

theorem centralizerProjection_state_square (p : AlgebraProjection M)
    (hc : ProductStateCentralizes M Ω p.val.val) (a : Algebra M) :
    vectorFunctional Ω (star a*a*p.val)=((‖a.val (p.val.val Ω)‖^2 : ℝ) : ℂ) := by
  have hh := hc (star a*a*p.val).val (star a*a*p.val).property
  change vectorFunctional Ω (p.val*(star a*a*p.val)) =
    vectorFunctional Ω ((star a*a*p.val)*p.val) at hh
  rw [mul_assoc (star a*a),p.property.isIdempotentElem.eq] at hh
  have he : star (a*p.val)*(a*p.val)=p.val*(star a*a*p.val) := by
    rw [star_mul,p.property.isSelfAdjoint.star_eq]
    simp only [mul_assoc]
  rw [← hh,← he,vectorFunctional_star_mul_self]
  simp only [MulMemClass.coe_mul,mul_apply_eq_comp,Complex.ofReal_pow]

theorem StateScales.coisometry_adjoint_vector_bound (d : ModularConjugationData M Ω)
    {r : ℝ} (hr : 0 < r) (v : Algebra M) (hv : v*star v=1)
    (hs : StateScales M Ω r v.val) (a : Algebra M) :
    r*‖a.val ((star v).val Ω)‖^2 ≤ ‖a.val Ω‖^2 := by
  let p : AlgebraProjection M := ⟨star v*v,⟨by
    change (star v*v)*(star v*v)=star v*v
    calc
      _ = star v*(v*star v)*v := by simp only [mul_assoc]
      _ = star v*v := by rw [hv,mul_one],
    IsSelfAdjoint.star_mul_self v⟩⟩
  have hp : ProductStateCentralizes M Ω p.val.val := hs.initial_centralizes v.property hr.ne'
  have hh := hs (star a*a*star v).val (star a*a*star v).property
  change vectorFunctional Ω ((star a*a*star v)*v)=
    (r : ℂ)*vectorFunctional Ω (v*(star a*a*star v)) at hh
  have he : v*(star a*a*star v)=star (a*star v)*(a*star v) := by
    simp only [star_mul,star_star,mul_assoc]
  rw [mul_assoc (star a*a),he,vectorFunctional_star_mul_self] at hh
  change vectorFunctional Ω (star a*a*p.val)=_ at hh
  rw [centralizerProjection_state_square p hp a] at hh
  have heq := congrArg Complex.re hh
  simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re,
    MulMemClass.coe_mul,mul_apply_eq_comp] at heq
  have hle := centralizerProjection_right_norm_le d p hp a
  nlinarith [norm_nonneg (a.val (p.val.val Ω)),norm_nonneg (a.val Ω)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalingAdjointCommutator
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform adjoint commutator control away from scaling ratio zero -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem StateScales.coisometry_adjoint_commutator_bound
    (d : ModularConjugationData M Ω) {r c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hcr : c ≤ r)
    (v : Algebra M) (hv : v*star v=1) (hs : StateScales M Ω r v.val)
    (a b : Algebra M) (hb : Commute b (star v)) :
    c*‖(a*star v-star v*a).val Ω‖ ≤ (1+c)*‖(a-b).val Ω‖ := by
  have hfirst := hs.coisometry_adjoint_vector_bound d (hc.trans_le hcr) v hv (a-b)
  have hcsq : c*‖(a-b).val ((star v).val Ω)‖^2 ≤ ‖(a-b).val Ω‖^2 :=
    (mul_le_mul_of_nonneg_right hcr (sq_nonneg _)).trans hfirst
  have hscaled : c*‖(a-b).val ((star v).val Ω)‖ ≤ ‖(a-b).val Ω‖ := by
    have hsquare : (c*‖(a-b).val ((star v).val Ω)‖)^2 ≤ ‖(a-b).val Ω‖^2 := by
      calc
        _ = c*(c*‖(a-b).val ((star v).val Ω)‖^2) := by ring
        _ ≤ c*‖(a-b).val Ω‖^2 := mul_le_mul_of_nonneg_left hcsq hc.le
        _ ≤ _ := mul_le_of_le_one_left (sq_nonneg _) hc1
    nlinarith [norm_nonneg ((a-b).val Ω),
      mul_nonneg hc.le (norm_nonneg ((a-b).val ((star v).val Ω)))]
  have hvnorm : ‖(star v).val‖ ≤ 1 := by
    change ‖star v‖ ≤ 1
    rw [norm_star]
    exact coisometry_norm_le v hv
  have hsecond : ‖(star v).val ((a-b).val Ω)‖ ≤ ‖(a-b).val Ω‖ :=
    ((star v).val.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hvnorm)
  have he : a*star v-star v*a=(a-b)*star v-star v*(a-b) := by
    rw [sub_mul,mul_sub,hb.eq]
    abel
  rw [he]
  change c*‖(a-b).val ((star v).val Ω)-(star v).val ((a-b).val Ω)‖ ≤ _
  calc
    _ ≤ c*(‖(a-b).val ((star v).val Ω)‖+‖(star v).val ((a-b).val Ω)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hc.le
    _ ≤ (1+c)*‖(a-b).val Ω‖ := by
      have hh := mul_le_mul_of_nonneg_left hsecond hc.le
      nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LocalScalingCentrality
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong centrality from local commutation and state scaling

The local algebras may contain an arbitrary first tensor factor; only
their density on the reference vector is used.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem local_scaling_adjoint_commutator_tendsto_oai
    (d : ModularConjugationData M Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (B : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : ∀ k, B k ≤ M.toStarSubalgebra)
    (hdense : ∀ a : Algebra M, ∀ ε : ℝ, 0 < ε →
      ∃ k, ∃ b : B k, ‖a.val Ω-b.val Ω‖ < ε)
    (s : ℕ → ℝ) (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales M Ω (s n) (v n).val)
    (hcomm : ∀ k, ∀ b : B k, ∀ n, k ≤ n → Commute b.val (v n).val)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcs : ∀ᶠ n in atTop, c ≤ s n)
    (a : Algebra M) (η : H) :
    Tendsto (fun n => (a*star (v n)-star (v n)*a).val η) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ‖a*star (v n)-star (v n)*a‖ ≤ 2*‖a‖ := by
    have hn : ‖star (v n)‖ ≤ 1 := by rw [norm_star]; exact coisometry_norm_le _ (hv n)
    calc
      _ ≤ ‖a*star (v n)‖+‖star (v n)*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖star (v n)‖+‖star (v n)‖*‖a‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith [norm_nonneg a]
  apply algebra_strong_tendsto_of_reference Ω
    (commutant_cyclic_of_separating_reference Ω hsep)
    (fun n => a*star (v n)-star (v n)*a) (2*‖a‖) (by positivity) hbound ?_ η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 2*(1+c) := by positivity
  obtain ⟨k,b,hb⟩ := hdense a (ε*c/(2*(1+c))) (by positivity)
  let bM : Algebra M := ⟨b.val,hB k b.property⟩
  filter_upwards [hcs,eventually_ge_atTop k] with n hcn hn
  have hcv : Commute (star bM) (v n) :=
    Subtype.ext (hcomm k ⟨star b.val,(B k).star_mem' b.property⟩ n hn).eq
  have hcvstar : Commute bM (star (v n)) := hcv.star_right
  have he := (hs n).coisometry_adjoint_commutator_bound d hc hc1 hcn
    (v n) (hv n) a bM hcvstar
  have hb' : ‖(a-bM).val Ω‖ < ε*c/(2*(1+c)) := hb
  have hm := (lt_div_iff₀ hden).mp hb'
  have hh : ‖(a*star (v n)-star (v n)*a).val Ω‖ < ε := by nlinarith
  simpa only [dist_zero_right] using hh

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.local_scaling_adjoint_commutator_tendsto_oai.{u_1} := @OAI.KadisonKastler.local_scaling_adjoint_commutator_tendsto_oai.{u_1}
