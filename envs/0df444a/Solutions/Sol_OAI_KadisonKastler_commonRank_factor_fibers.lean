-- Prove2me | solution 1 for OAI.KadisonKastler.commonRank_factor_fibers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:20:00.010642+00:00
-- url     : https://prove2.me/submissions/3d8f873b-8ac3-4d7a-88a9-6bb0da45a986

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
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
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
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
import Definitions.Def_Q260K019
import Theorems.Thm_OAI_KadisonSimilarity_ae_common_fiber_scalar_center
import Theorems.Thm_OAI_KadisonKastler_representationVonNeumannAlgebra_eq_generated

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RepresentationCenterTransport
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar centers and exact representation conjugacy

An algebra equivalence between the ambient operator algebras transports
the represented bicommutants and their centers. In particular, identifying
two equal projection ranges does not change the factor-fiber criterion.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem representation_bicommutant_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    θ T ∈ representationVonNeumannAlgebra ρ := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT ⊢
  intro Q hQ
  have hpre : θ.symm Q ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
    rintro _ ⟨a, rfl⟩
    apply θ.injective
    change θ (σ a * θ.symm Q) = θ (θ.symm Q * σ a)
    simp only [map_mul]
    change θ (σ a) * θ (θ.symm Q) = θ (θ.symm Q) * θ (σ a)
    rw [θ.apply_symm_apply, hθ]
    exact hQ (ρ a) ⟨a, rfl⟩
  have h := congrArg θ (hT (θ.symm Q) hpre)
  simpa only [map_mul, θ.apply_symm_apply] using h

theorem representation_commutant_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ (representationVonNeumannAlgebra σ).commutant) :
    θ T ∈ (representationVonNeumannAlgebra ρ).commutant := by
  apply (mem_representation_commutant_iff ρ (θ T)).mpr
  have ht := (mem_representation_commutant_iff σ T).mp hT
  rintro _ ⟨a, rfl⟩
  change ρ a * θ T = θ T * ρ a
  simpa only [map_mul, hθ] using congrArg θ (ht (σ a) ⟨a, rfl⟩)

theorem representation_center_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra σ)) :
    θ T ∈ vonNeumannCenter (representationVonNeumannAlgebra ρ) :=
  ⟨representation_bicommutant_map_mem θ σ ρ hθ T hT.1,
    representation_commutant_map_mem θ σ ρ hθ T hT.2⟩

/-- The scalar-center condition used for factor fibers is unchanged by an
exact star-algebra conjugacy of the representations. -/
theorem scalar_center_of_representation_equiv
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (hρ : ∀ a : (representationVonNeumannAlgebra ρ).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c) :
    ∀ a : (representationVonNeumannAlgebra σ).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  intro a ha
  have haCenter : (a : H →L[ℂ] H) ∈
      vonNeumannCenter (representationVonNeumannAlgebra σ) := by
    refine ⟨a.property, VonNeumannAlgebra.mem_commutant_iff.mpr ?_⟩
    intro b hb
    exact (congrArg Subtype.val (ha ⟨b, hb⟩)).symm
  have hθCenter := representation_center_map_mem θ σ ρ hθ a haCenter
  let aρ : (representationVonNeumannAlgebra ρ).toStarSubalgebra := ⟨θ a, hθCenter.1⟩
  have hcomm : ∀ b, aρ * b = b * aρ := by
    intro b
    apply Subtype.ext
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hθCenter.2) b b.property).symm
  obtain ⟨c, hc⟩ := hρ aρ hcomm
  refine ⟨c, Subtype.ext ?_⟩
  apply θ.injective
  have hval := congrArg Subtype.val hc
  change θ (a : H →L[ℂ] H) = algebraMap ℂ (K →L[ℂ] K) c at hval
  change θ (a : H →L[ℂ] H) = θ (algebraMap ℂ (H →L[ℂ] H) c)
  simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] using hval

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_JointCStarSource
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common separable source for an algebra and its commutant

Taking the norm closure of the joint star algebra preserves norm separability.
When the two sources generate `P` and `P'`, the common source generates the
commutant of the center. This puts both sources in one fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

theorem jointCStarSource_minimal (B C S : StarSubalgebra ℂ A)
    (hB : B ≤ S) (hC : C ≤ S) (hS : IsClosed (S : Set A)) :
    jointCStarSource B C ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (sup_le hB hC) hS

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GlobalFiberRestriction
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and zero extension of range representations

The old-unit projection is unchanged by restriction along a unital map,
even when the represented map is nonunital. Restriction commutes with
zero extension from a conull base, so the canonical range identifications
are available at every base point, including the zero fibers.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem nonunitalRestrictionFiberEquiv_intertwines (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (b : B)
    (v : projectionFiber (nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom))
      (nonunitalUnitProjection_isStarProjection (τ.comp φ.toNonUnitalStarAlgHom))) :
    nonunitalRestrictionFiberEquiv φ τ
        (nonunitalRangeRepresentation (τ.comp φ.toNonUnitalStarAlgHom) b v) =
      nonunitalRangeRepresentation τ (φ b) (nonunitalRestrictionFiberEquiv φ τ v) := by
  apply Subtype.ext
  simp only [nonunitalRestrictionFiberEquiv_coe, nonunitalRangeRepresentation_coe,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FixedFiberFactors
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar centers transported from the actual range to fixed coordinates -/

namespace KadisonKastler

open KadisonSimilarity
open scoped lp

noncomputable section

variable {X A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : X → B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

theorem fixedFiber_scalarCenter_of_range (ι : A →⋆ₐ[ℂ] B) (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n)
    (hfactor : ∀ a : (representationVonNeumannAlgebra
        (nonunitalRangeRepresentation ((ρ x.val).comp ι.toNonUnitalStarAlgHom))).toStarSubalgebra,
      (∀ c, a * c = c * a) → ∃ z : ℂ, a = algebraMap ℂ _ z) :
    ScalarCenter (generatedVonNeumannAlgebra
      ((fixedFiberRepresentation ρ b hb n x).comp ι).range) := by
  let : CompleteSpace (representationUnitProjection ρ x.val).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (representationUnitProjection_idempotent ρ x.val)).completeSpace_coe
  let old := nonunitalRangeRepresentation ((ρ x.val).comp ι.toNonUnitalStarAlgHom)
  let new := (fixedFiberRepresentation ρ b hb n x).comp ι
  let e := (nonunitalRestrictionFiberEquiv ι (ρ x.val)).trans
    (projectionStratumCoordinates (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb n x)
  have he (a : A) : e.conjStarAlgEquiv (old a) = new a := by
    apply ContinuousLinearMap.ext
    intro v
    change (projectionStratumCoordinates (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb n x)
        (nonunitalRestrictionFiberEquiv ι (ρ x.val)
          (old a (e.symm v))) = new a v
    rw [nonunitalRestrictionFiberEquiv_intertwines]
    change (projectionStratumCoordinates (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb n x)
        (nonunitalRangeRepresentation (ρ x.val) (ι a)
          ((projectionStratumCoordinates (representationUnitProjection ρ)
            (representationUnitProjection_idempotent ρ) b hb n x).symm v)) = new a v
    rfl
  have hnew : ∀ a : (representationVonNeumannAlgebra new).toStarSubalgebra,
      (∀ c, a * c = c * a) → ∃ z : ℂ, a = algebraMap ℂ _ z := by
    apply scalar_center_of_representation_equiv e.symm.conjStarAlgEquiv new old
    · intro a
      apply e.conjStarAlgEquiv.injective
      change e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (new a)) = e.conjStarAlgEquiv (old a)
      rw [StarAlgEquiv.apply_symm_apply, he]
    · exact hfactor
  intro T hT hcentral
  have hT' : T ∈ representationVonNeumannAlgebra new := by
    rw [representationVonNeumannAlgebra_eq_generated]
    exact hT
  let a : (representationVonNeumannAlgebra new).toStarSubalgebra := ⟨T, hT'⟩
  obtain ⟨z, hz⟩ := hnew a (fun c => Subtype.ext (by
    exact (hcentral c.val (by
      rw [← representationVonNeumannAlgebra_eq_generated]
      exact c.property)).symm))
  refine ⟨z, ?_⟩
  have hv := congrArg Subtype.val hz
  change T = algebraMap ℂ (ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ]
    ℓ²(projectionDimensionIndex n, ℂ)) z at hv
  simpa only [Algebra.algebraMap_eq_smul_one] using hv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitizedCommonFields
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Everywhere-defined fields and conull unitization -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {X A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem zeroExtend_starLift_univ (ρ : X → B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : X) :
    zeroExtendNonunitalRepresentation Set.univ
      (fun y => Unitization.starLift (ρ y.val)) x = ρ x := by
  classical
  unfold zeroExtendNonunitalRepresentation
  rw [dite_eq_left (Set.mem_univ x)]
  change Unitization.starLift.symm (Unitization.starLift (ρ x)) = ρ x
  exact Unitization.starLift.left_inv (ρ x)

theorem zeroExtend_restrict_starLift_univ (ρ : X → B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ι : A →⋆ₐ[ℂ] B) (x : X) :
    zeroExtendNonunitalRepresentation Set.univ
      (fun y => unitizationRestrict ι (Unitization.starLift (ρ y.val))) x =
      (ρ x).comp ι.toNonUnitalStarAlgHom := by
  rw [zeroExtend_unitizationRestrict, zeroExtend_starLift_univ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonunitalFiberCenter
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar centers of nonunital representation ranges

These adapters keep the range Hilbert space and its unit projection inside
one definition when a common source is restricted to a smaller algebra.
-/

namespace KadisonKastler

open KadisonSimilarity
open scoped lp

noncomputable section

variable {X A B C K : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem nonunitalFiberScalarCenter_restrict_starLift
    (ρ : X → B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ι : A →⋆ₐ[ℂ] B) (x : X)
    (h : NonunitalFiberScalarCenter (zeroExtendNonunitalRepresentation Set.univ
      (fun y => unitizationRestrict ι (Unitization.starLift (ρ y.val))) x)) :
    NonunitalFiberScalarCenter ((ρ x).comp ι.toNonUnitalStarAlgHom) := by
  rwa [zeroExtend_restrict_starLift_univ] at h

theorem fixedFiber_scalarCenter_of_nonunital
    (ρ : X → B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (b : ℕ → K) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (ι : A →⋆ₐ[ℂ] B) (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n)
    (h : NonunitalFiberScalarCenter ((ρ x.val).comp ι.toNonUnitalStarAlgHom)) :
    ScalarCenter (generatedVonNeumannAlgebra ((fixedFiberRepresentation ρ b hb n x).comp ι).range) :=
  fixedFiber_scalarCenter_of_range ρ b hb ι n x h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonFiberCenterPredicate
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The common-fiber theorem as a range-center predicate -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u} [CommCStarAlgebra Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem ae_common_nonunital_fiber_center
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hcomm : ∀ a : A, ∀ c : C, a.val * c.val = c.val * a.val)
    (hgen : representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ Z)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource A C) →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ a : jointCStarSource A C, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap Subtype.val (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) a.val f x =
          ρ x (Unitization.inr a) (f x)) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      NonunitalFiberScalarCenter (zeroExtendNonunitalRepresentation s
        (fun y => unitizationRestrict
          (StarSubalgebra.inclusion (le_jointCStarSource_left A C)) (ρ y)) x) :=
  ae_common_fiber_scalar_center π D A C hcomm hgen s hs hnull ρ hρ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonModelFactorFibers
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Scalar centers of the actual common-model range fibers -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u} [CommCStarAlgebra Z] [TopologicalSpace.SeparableSpace Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
  [TopologicalSpace.SeparableSpace S] (M : BorelCommonModel π D S.subtype)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

omit [TopologicalSpace.SeparableSpace Z] [TopologicalSpace.SeparableSpace S] in
theorem commonModel_factor_fibers
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hAS : A ≤ S) (hCS : C ≤ S)
    (hcomm : ∀ a : A, ∀ c : C, a.val * c.val = c.val * a.val)
    (hgen : representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      starSubalgebraCommutant π.range) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      NonunitalFiberScalarCenter ((M.field x).comp
        (StarSubalgebra.inclusion hAS).toNonUnitalStarAlgHom) := by
  let hJS := jointCStarSource_minimal A C S hAS hCS inferInstance
  let φ := StarSubalgebra.inclusion hJS
  let ρ := fun x => (M.field x).comp φ.toNonUnitalStarAlgHom
  let ρu := fun x : (Set.univ : Set (WeakDual.characterSpace ℂ Z)) => Unitization.starLift (ρ x.val)
  have hρ (a : jointCStarSource A C) (f : CommonCyclicHilbert π D) :
      ∀ᵐ x : (Set.univ : Set (WeakDual.characterSpace ℂ Z))
        ∂Measure.comap Subtype.val (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) a.val f x =
          ρu x (Unitization.inr a) (f x) := by
    have ha := (ae_restrict_iff_subtype MeasurableSet.univ).mp
      (ae_restrict_of_ae (M.action (φ a) f))
    filter_upwards [ha] with x hx
    have he : ρu x (Unitization.inr a) = M.field x.val (φ a) :=
      DFunLike.congr_fun (Unitization.starLift.left_inv (ρ x.val)) a
    rw [he]
    exact hx
  have hf := ae_common_nonunital_fiber_center π D A C hcomm hgen Set.univ
    MeasurableSet.univ (by simp) ρu hρ
  have hi : φ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left A C)) =
      StarSubalgebra.inclusion hAS := by
    apply StarAlgHom.ext
    intro a
    rfl
  apply hf.mono
  intro x hx
  have h := nonunitalFiberScalarCenter_restrict_starLift ρ
    (StarSubalgebra.inclusion (le_jointCStarSource_left A C)) x hx
  change NonunitalFiberScalarCenter ((M.field x).comp
    (φ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left A C))).toNonUnitalStarAlgHom) at h
  rwa [hi] at h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankFactorFibers
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Factor fibers for a source and its commuting generating source -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u} [CommCStarAlgebra Z] [TopologicalSpace.SeparableSpace Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
  [TopologicalSpace.SeparableSpace S] (M : BorelCommonModel π D S.subtype)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

attribute [local instance] OAI.KadisonKastler.rankFactorCoordinateMeasurable
local instance rankFactorCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

omit [TopologicalSpace.SeparableSpace Z] [TopologicalSpace.SeparableSpace S] in
theorem commonRank_factor_fibers_oai
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hAS : A ≤ S) (hCS : C ≤ S)
    (hcomm : ∀ a : A, ∀ c : C, a.val * c.val = c.val * a.val)
    (hgen : representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      starSubalgebraCommutant π.range) (n : ℕ) :
    ∀ᵐ x ∂projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) n,
      ScalarCenter (commonRankFiberAlgebra M (StarSubalgebra.inclusion hAS) n x) := by
  have hf := commonModel_factor_fibers S M A C hAS hCS hcomm hgen
  have hr := (ae_restrict_iff_subtype (measurableSet_projectionRankStratum
    (commonModelProjection M) (commonRankBasis π D) (commonModelProjection_measurable M) n)).mp
    (ae_restrict_of_ae hf)
  filter_upwards [hr] with x hx
  rw [commonRankFiberAlgebra, representationVonNeumannAlgebra_eq_generated]
  exact fixedFiber_scalarCenter_of_nonunital M.field (commonRankBasis π D) (commonRankBasis_total π D)
    (StarSubalgebra.inclusion hAS) n x hx

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.commonRank_factor_fibers_oai.{u} := @OAI.KadisonKastler.commonRank_factor_fibers_oai.{u}
