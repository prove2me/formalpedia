-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_expected_matrix_typeIII1_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:06:35.304754+00:00
-- url     : https://prove2.me/submissions/ae8ec658-7d98-4d0f-946b-314737a7c920

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
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
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
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Data.Finset.Sort
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
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
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K037
import Definitions.Def_Q260K039
import Theorems.Thm_OAI_KadisonKastler_MatrixNearInclusion_mono
import Theorems.Thm_OAI_KadisonKastler_ModularConjugationData_expected_right_data
import Theorems.Thm_OAI_KadisonKastler_TypeIII1Factor_of_normalStarAlgEquiv
import Theorems.Thm_OAI_KadisonKastler_boundedWeakNormal_starEquiv_trans
import Theorems.Thm_OAI_KadisonKastler_exists_matrixStagePair_preparation
import Theorems.Thm_OAI_KadisonKastler_generated_matrixStages_eq
import Theorems.Thm_OAI_KadisonKastler_matrixStageConcreteUnits_algebra
import Theorems.Thm_OAI_KadisonKastler_nearConjugacy_of_matrixPair_preparation
import Theorems.Thm_OAI_KadisonKastler_publishedBlockCommutantApproximation
import Theorems.Thm_OAI_KadisonKastler_uniform_prepared_matrix_strong_stability
import Theorems.Thm_OAI_KadisonKastler_unitaryConjugateEquiv_boundedWeakNormal

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedMatrixStability
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.centralRefinementIterates_succ _root_.OAI.KadisonKastler.centralRefinementIterates_zero _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialMatrixAmplification_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Stability from an expected irreducible increasing matrix algebra

The actual two amenable corrections prepare the common left and right
matrix algebras. The corrected neighbor remains type III₁ by core
isomorphism, and its cyclic separating vector supplies the modular data
for prepared matrix stability. All tolerances precede the algebras and
the expectation data; no trace is required on either ambient factor.
-/

namespace KadisonKastler

open Generator

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.expectedStabilityOrder
local instance expectedStabilityStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

section Transport

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.expectedStabilityOrder
private theorem corrected_neighbor_typeIII1
    (N : VonNeumannAlgebra H) (hN : TypeIII1Factor N)
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hc : DenseRange (algebraVectorMap N Ω))
    (hs : Function.Injective (algebraVectorMap N Ω))
    (m : ModularSpectralResolution N Ω) (a b : unitary (H →L[ℂ] H)) :
    TypeIII1Factor (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) := by
  let e := unitaryConjugateEquiv (star a) N
  let f := unitaryConjugateEquiv (star b) (unitaryConjugateAlgebra (star a) N)
  exact hN.of_normalStarAlgEquiv (e.trans f)
    (boundedWeakNormal_starEquiv_trans e f
      (unitaryConjugateEquiv_boundedWeakNormal N (star a))
      (unitaryConjugateEquiv_boundedWeakNormal (unitaryConjugateAlgebra (star a) N) (star b)))
    Ω hΩ hc hs m

private theorem corrected_neighbor_core
    (N : VonNeumannAlgebra H) (hN : TypeIII1Factor N)
    (ΩN : H) (hΩN : ‖ΩN‖ = 1) (hcN : DenseRange (algebraVectorMap N ΩN))
    (hsN : Function.Injective (algebraVectorMap N ΩN))
    (mN : ModularSpectralResolution N ΩN) (a b : unitary (H →L[ℂ] H))
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hc : DenseRange (algebraVectorMap
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) Ω))
    (hs : Function.Injective (algebraVectorMap
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) Ω))
    (n : ModularSpectralResolution
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) Ω) :
    TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N))) := by
  apply (corrected_neighbor_typeIII1 N hN ΩN hΩN hcN hsN mN a b).core_type
    Ω hΩ hc hs n.group n.continuous
  · intro t x hx
    change unitaryConj (n.group t) x ∈
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N) :
        Set (H →L[ℂ] H))
    rw [← n.normalizes t]
    exact Set.mem_image_of_mem _ hx
  · exact n.isModular

end Transport

/-- Two type III₁ factors are strongly close when the source has the
specified expected irreducible increasing matrix algebra and the pair
is close on all matrix unit balls. The tolerance is independent of all
representation, vector and expectation data. -/
theorem uniform_expected_matrix_typeIII1_stability_oai
    (h : ModularCorePublishedInputs.{u})
    (hModular : PublishedModularSpectralResolution.{u})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIII1Factor M → TypeIII1Factor N →
      ∀ (A : ℕ → FiniteMatrixStage M),
        Monotone (fun n => (A n).units.concreteAlgebra) →
      ∀ (τ : FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann A)))
        (P : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann A)), P 1 = 1 →
      (∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
        P (StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * x) =
          r * P x) →
      (∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
        P (x * StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) =
          P x * r) →
      ∀ (Ω : H), (∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω)) →
        DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
      (∀ T ∈ M, (∀ r ∈ FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) →
      ∀ (ΩN : H), ‖ΩN‖ = 1 → DenseRange (algebraVectorMap N ΩN) →
        Function.Injective (algebraVectorMap N ΩN) →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
        MatrixNearInclusion M N γ → MatrixNearInclusion N M γ → NearConjugacy M N ε := by
  obtain ⟨t, ht, hstable⟩ := uniform_prepared_matrix_strong_stability h (half_pos hε)
  refine ⟨min (1 / 200000) (min (t / 90902) (ε / 90900)),
    lt_min (by norm_num) (lt_min (div_pos ht (by norm_num))
      (div_pos hε (by norm_num))), ?_⟩
  intro H _ _ _ _ _ M N hM hN A hA τ P hP hleft hright Ω hstate hcM hsM hirr
    ΩN hΩN hcN hsN γ hγ hsmall hgap hMN hNM
  have hprepare : γ < 1 / 200000 := hsmall.trans_le (min_le_left _ _)
  have hscale : 90902 * γ < t := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hx' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 90902)).mp hx
    linarith
  have hcost : 45450 * γ + ε / 2 < ε := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hx' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 90900)).mp hx
    linarith
  obtain ⟨d, m⟩ := (hModular H M Ω hcM hsM).some
  let mN : ModularSpectralResolution N ΩN := (hModular H N ΩN hcN hsN).some.2
  obtain ⟨a, b, ha, hb, hRN, hSN, hMN₂, hN₂M, hgap₂, hc₂, hs₂, _, _⟩ :=
    exists_matrixStagePair_preparation
      (fun M => publishedBlockCommutantApproximation (Algebra M) H)
      M N A hA τ P hP hleft hright Ω hstate d hirr
      hγ hprepare hgap hMN hNM
  let N₂ := unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)
  obtain ⟨hnorm, hrightM, hvector⟩ := d.expected_right_data
    (FiniteMatrixStage.generatedVonNeumann_le A) τ P hP hleft hright hstate
  let n : ModularSpectralResolution N₂ Ω := (hModular H N₂ Ω hc₂ hs₂).some.2
  have hNcore : TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous N₂) :=
    corrected_neighbor_core N hN ΩN hΩN hcN hsN mN a b Ω hnorm hc₂ hs₂ n
  have hrightN : ∀ r ∈ FiniteMatrixStage.generatedVonNeumann A,
      conjugationOperator d.conjugation r ∈ N₂.commutant := by
    intro r hr
    apply hSN
    change conjugationOperator d.conjugation r ∈
      (conjugateRightAlgebra d.conjugation d.involutive
        (FiniteMatrixStage.generatedVonNeumann A) : Set (H →L[ℂ] H))
    rw [conjugateRightAlgebra_coe]
    exact ⟨r, hr, rfl⟩
  have hmonotone : 90901 * γ ≤ 90902 * γ := by nlinarith
  have hv : NearConjugacy M N₂ (ε / 2) :=
    hstable H M N₂ (FiniteMatrixStage.generatedVonNeumann A) hM.toTypeIIIFactor
      Ω m n d.conjugation d.involutive hnorm hNcore
      (fun i => (A i).size) (matrixStageConcreteUnits A)
      (by simpa only [matrixStageConcreteUnits_algebra] using hA)
      (generated_matrixStages_eq A hA) (FiniteMatrixStage.generatedVonNeumann_le A) hRN
      hirr hrightM hrightN hvector (90902 * γ) (by positivity) hscale hgap₂
      (hMN₂.mono hmonotone) (hN₂M.mono hmonotone)
  obtain ⟨v, hv, hnormv⟩ := nearConjugacy_of_matrixPair_preparation M N a b ha hb hv
  exact ⟨v, hv, hnormv.trans hcost⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_expected_matrix_typeIII1_stability_oai.{u} := @OAI.KadisonKastler.uniform_expected_matrix_typeIII1_stability_oai.{u}
