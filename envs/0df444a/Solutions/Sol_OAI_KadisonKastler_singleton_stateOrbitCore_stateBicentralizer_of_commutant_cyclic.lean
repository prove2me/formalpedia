-- Prove2me | solution 1 for OAI.KadisonKastler.singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:33:36.1231+00:00
-- url     : https://prove2.me/submissions/e75c8e92-39f3-4402-b386-f76290a43e18

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
import Mathlib.Algebra.QuadraticDiscriminant
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
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
import Mathlib.Analysis.Complex.Norm
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_KadisonKastler_stateBicentralizerMember_iff_unitary_tests
import Theorems.Thm_OAI_KadisonKastler_stateConjugate_vector_norm_sq_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateOrbitCompact
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Compact asymptotic state-central orbit hulls

The intersection of the decreasing weakly closed convex hulls contains
the original operator and remains in its operator-norm ball.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem weakOperatorBall_convex (M : VonNeumannAlgebra H) (r : ℝ) :
    Convex ℝ (weakOperatorBall M r) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨M.toStarSubalgebra.add_mem
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hX.1 a)
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hY.1 b),?_⟩
  have h := (convex_closedBall (0 : H →L[ℂ] H) r)
    (show X.toCLM ∈ Metric.closedBall 0 r by simpa using hX.2)
    (show Y.toCLM ∈ Metric.closedBall 0 r by simpa using hY.2) ha hb hab
  simpa using h

theorem stateOrbitHull_subset_ball (ξ : H) (a : Algebra M) (δ : ℝ) :
    closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) ⊆ weakOperatorBall M ‖a‖ := by
  apply closedConvexHull_min ?_ (weakOperatorBall_convex M ‖a‖)
    (weakOperatorBall_isCompact M ‖a‖).isClosed
  rintro T ⟨u,_,rfl⟩
  refine ⟨(star u.val*a*u.val).property,?_⟩
  change ‖star u.val*a*u.val‖ ≤ ‖a‖
  calc
    _ ≤ ‖star u.val*a‖*‖u.val‖ := norm_mul_le _ _
    _ ≤ ‖star u.val*a‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_unitary_le_one u)
    _ ≤ ‖star u.val‖*‖a‖ := norm_mul_le _ _
    _ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_unitary_le_one (star u))

theorem stateOrbitHull_compact (ξ : H) (a : Algebra M) (δ : ℝ) :
    IsCompact (closedConvexHull ℝ (stateUnitaryOrbit ξ a δ)) :=
  (weakOperatorBall_isCompact M ‖a‖).of_isClosed_subset isClosed_closedConvexHull
    (stateOrbitHull_subset_ball ξ a δ)

theorem stateOrbitHull_mono (ξ : H) (a : Algebra M) {δ ε : ℝ} (h : δ ≤ ε) :
    closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) ⊆
      closedConvexHull ℝ (stateUnitaryOrbit ξ a ε) := by
  apply (closedConvexHull ℝ).monotone
  rintro T ⟨u,hu,hT⟩
  exact ⟨u,hu.trans h,hT⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateOrbitNeighborhood
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Neighborhood control by asymptotic state-central hulls -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_stateOrbitHull_subset_open (ξ : H) (a : Algebra M)
    {U : Set (H →WOT[ℂ] H)} (hU : IsOpen U) (hcore : stateOrbitCore ξ a ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) ⊆ U := by
  let I := {δ : ℝ // 0 < δ}
  let t : I → Set (H →WOT[ℂ] H) :=
    fun δ => closedConvexHull ℝ (stateUnitaryOrbit ξ a δ.val)
  let K := closedConvexHull ℝ (stateUnitaryOrbit ξ a 1) ∩ Uᶜ
  let : Nonempty I := ⟨⟨1,zero_lt_one⟩⟩
  have hK : IsCompact K := (stateOrbitHull_compact ξ a 1).inter_right hU.isClosed_compl
  have hdis : Disjoint K (⋂ δ : I, t δ) := by
    apply Set.disjoint_left.mpr
    intro T hTK hT
    apply hTK.2
    apply hcore
    intro δ hδ
    exact Set.mem_iInter.mp hT ⟨δ,hδ⟩
  have hdir : Directed (· ⊇ ·) t := by
    intro δ ε
    refine ⟨⟨min δ.val ε.val,lt_min δ.property ε.property⟩,?_,?_⟩
    · exact stateOrbitHull_mono ξ a (min_le_left _ _)
    · exact stateOrbitHull_mono ξ a (min_le_right _ _)
  obtain ⟨δ,hδ⟩ := hK.elim_directed_family_closed t (fun _ => isClosed_closedConvexHull)
    (Set.disjoint_iff_inter_eq_empty.mp hdis) hdir
  refine ⟨min δ.val 1,lt_min δ.property zero_lt_one,?_⟩
  intro T hT
  by_contra hnot
  apply Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hδ) (show T ∈ K from
    ⟨stateOrbitHull_mono ξ a (min_le_right _ _) hT,hnot⟩)
  exact stateOrbitHull_mono ξ a (min_le_left _ _) hT

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateOrbitSingleton
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform unitary tests from a singleton asymptotic orbit hull -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem unitary_commutator_vector_norm_eq (ξ : H) (a : Algebra M)
    (u : unitary (Algebra M)) :
    ‖(u.val*a-a*u.val).val ξ‖=‖(star u.val*a*u.val).val ξ-a.val ξ‖ := by
  have he : u.val.val ((star u.val*a*u.val).val ξ-a.val ξ) =
      -(u.val*a-a*u.val).val ξ := by
    change u.val.val (((star u.val*a*u.val).val-a.val) ξ) = _
    rw [← mul_apply_eq_comp]
    have ha : u.val*(star u.val*a*u.val-a) = -(u.val*a-a*u.val) := by
      rw [mul_sub,← mul_assoc,← mul_assoc,u.property.2,one_mul]
      abel
    exact congrArg (fun b : Algebra M => b.val ξ) ha
  have h := Unitary.norm_map (ambientAlgebraUnitary u)
    ((star u.val*a*u.val).val ξ-a.val ξ)
  change ‖u.val.val ((star u.val*a*u.val).val ξ-a.val ξ)‖=_ at h
  rwa [he,norm_neg] at h

theorem singleton_stateOrbitCore_unitary_control (ξ : H) (a : Algebra M)
    (hcore : stateOrbitCore ξ a={ContinuousLinearMapWOT.ofCLM a.val})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : unitary (Algebra M),
      ‖vectorStateCommutator ξ u.val‖ ≤ δ → ‖(u.val*a-a*u.val).val ξ‖ < ε := by
  let U : Set (H →WOT[ℂ] H) :=
    {T | ‖a.val ξ‖^2-ε^2/4 < (inner ℂ (a.val ξ) (T ξ)).re}
  have hU : IsOpen U := isOpen_lt continuous_const
    (Complex.continuous_re.comp (ContinuousLinearMapWOT.continuous_inner_apply
      continuous_id ξ (a.val ξ)))
  have hsub : stateOrbitCore ξ a ⊆ U := by
    intro T hT
    rw [hcore,Set.mem_singleton_iff] at hT
    subst T
    change ‖a.val ξ‖^2-ε^2/4 < (inner ℂ (a.val ξ) (a.val ξ)).re
    rw [inner_self_eq_norm_sq_to_K]
    have hre (r : ℝ) : ((r : ℂ)^2).re=r^2 := by
      norm_num [pow_two,Complex.mul_re]
    change ‖a.val ξ‖^2-ε^2/4 < ((‖a.val ξ‖ : ℂ)^2).re
    rw [hre]
    nlinarith only [sq_pos_of_pos hε]
  obtain ⟨d,hd,hdU⟩ := exists_stateOrbitHull_subset_open ξ a hU hsub
  let δ := min d (ε^2/(4*(‖a‖^2+1)))
  have hδ : 0 < δ := lt_min hd (div_pos (sq_pos_of_pos hε) (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro u hu
  let T := ContinuousLinearMapWOT.ofCLM (star u.val*a*u.val).val
  have hT : T ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a d) :=
    subset_closedConvexHull ⟨u,hu.trans (min_le_left _ _),rfl⟩
  have hi : ‖a.val ξ‖^2-ε^2/4 < (inner ℂ (a.val ξ) (T ξ)).re := hdU hT
  have hv := stateConjugate_vector_norm_sq_le ξ a u
  have hdn : ‖vectorStateCommutator ξ u.val‖*(4*(‖a‖^2+1)) ≤ ε^2 :=
    (le_div_iff₀ (by positivity)).mp (hu.trans (min_le_right _ _))
  have hprod : ‖vectorStateCommutator ξ u.val‖*‖a‖^2 ≤ ε^2/4 := by
    nlinarith only [hdn,norm_nonneg (vectorStateCommutator ξ u.val)]
  have hs := norm_sub_sq (𝕜 := ℂ) (a.val ξ) (T ξ)
  change ‖a.val ξ-T ξ‖^2 = ‖a.val ξ‖^2-
    2*(inner ℂ (a.val ξ) (T ξ)).re+‖T ξ‖^2 at hs
  rw [unitary_commutator_vector_norm_eq,norm_sub_rev]
  change ‖a.val ξ-T ξ‖ < ε
  change ‖T ξ‖^2 ≤ _ at hv
  nlinarith only [hi,hv,hprod,hs,hε,norm_nonneg (a.val ξ-T ξ)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongReferenceTests
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_StateOrbitBicentralizer
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A singleton asymptotic orbit hull gives a bicentralizer element

The unitary estimates extend from the reference vector to every ambient
vector through the dense commutant orbit and uniform operator bounds.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic_oai
    (ξ : H) (hcyc : DenseRange (algebraVectorMap M.commutant ξ)) (a : Algebra M)
    (hcore : stateOrbitCore ξ a={ContinuousLinearMapWOT.ofCLM a.val}) :
    stateBicentralizerMember ξ a := by
  apply (stateBicentralizerMember_iff_unitary_tests ξ a).mpr
  intro u hu η
  let T (n : ℕ) : Algebra M := a*(u n).val-(u n).val*a
  have htξ : Tendsto (fun n => (T n).val ξ) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := singleton_stateOrbitCore_unitary_control ξ a hcore ε hε
    filter_upwards [hu.eventually (gt_mem_nhds hδ)] with n hn
    have h := hd (u n) hn.le
    change ‖(u n).val.val (a.val ξ)-a.val ((u n).val.val ξ)‖ < ε at h
    change dist (a.val ((u n).val.val ξ)-(u n).val.val (a.val ξ)) 0 < ε
    simpa only [dist_zero_right,norm_sub_rev] using h
  have ht : ∀ n, ‖T n‖ ≤ 2*‖a‖ := by
    intro n
    have hunit := norm_unitary_le_one (u n)
    calc
      _ ≤ ‖a*(u n).val‖+‖(u n).val*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖(u n).val‖+‖(u n).val‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith only [hunit,norm_nonneg a]
  exact algebra_strong_tendsto_of_reference ξ
    hcyc T (2*‖a‖)
      (by positivity) ht htξ η

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic_oai.{u_1} := @OAI.KadisonKastler.singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic_oai.{u_1}
