-- Prove2me | solution 1 for OAI.KadisonKastler.exists_finite_two_vector_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:51:58.156315+00:00
-- url     : https://prove2.me/submissions/b7aec007-5b72-4cb6-82ec-ddd0cbd9ec98

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
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
import Definitions.Def_Q260K032
import Theorems.Thm_OAI_KadisonKastler_finiteOutwardProjection_gap_integrable
import Theorems.Thm_OAI_KadisonKastler_finiteOutwardProjection_integral_lower
import Theorems.Thm_OAI_KadisonKastler_finiteOutwardProjection_integral_mass
import Theorems.Thm_OAI_KadisonKastler_finiteOutwardProjection_integral_upper_sq
import Theorems.Thm_OAI_KadisonKastler_finiteOutwardProjection_mass_integrable

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateFiniteThreshold
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite spectral cuts and the conjugate right action -/

namespace KadisonKastler

open Generator Generator.Tracial Finset
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

omit [CompleteSpace H] [Fintype ι] in
theorem conjugationOperator_finsetSum (J : H ≃ₗᵢ⋆[ℂ] H)
    (s : Finset ι) (P : ι → H →L[ℂ] H) :
    conjugationOperator J (∑ i ∈ s, P i) = ∑ i ∈ s, conjugationOperator J (P i) := by
  ext ξ
  simp only [conjugationOperator_apply,_root_.sum_apply,map_sum]

omit [CompleteSpace H] in
theorem conjugationOperator_real_sum (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → H →L[ℂ] H) (c : ι → ℝ) :
    conjugationOperator J (∑ i, (c i : ℂ) • P i) =
      ∑ i, (c i : ℂ) • conjugationOperator J (P i) := by
  rw [conjugationOperator_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugationOperator_smul]
  simp only [Complex.star_def,Complex.conj_ofReal]

omit [CompleteSpace H] in
theorem conjugationOperator_finiteThreshold (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) :
    conjugationOperator J (finiteThresholdProjection P c t) =
      finiteThresholdProjection (fun i => conjugationOperator J (P i)) c t :=
  conjugationOperator_real_sum J P _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoVectorCutSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Choosing a projection from two relative mean bounds -/

namespace KadisonKastler

open MeasureTheory Generator Generator.Tracial

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_two_relative_bounds (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hh₀ : ∀ x, 0 ≤ h x)
    {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hmean : α*(∫ x, f x ∂μ)+K*(∫ x, h x ∂μ) < α*K*(∫ x, g x ∂μ)) :
    ∃ x, f x < K*g x ∧ h x < α*g x := by
  have hint : 0 < ∫ x, α*K*g x-(α*f x+K*h x) ∂μ := by
    have he := integral_sub (hg.const_mul (α*K)) ((hf.const_mul α).add (hh.const_mul K))
    simp only [Pi.add_apply] at he
    rw [he,integral_add (hf.const_mul _) (hh.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul]
    linarith
  obtain ⟨x,hx⟩ : ∃ x, 0 < α*K*g x-(α*f x+K*h x) := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hint) (integral_nonpos hn)
  refine ⟨x,?_,?_⟩
  · have hn := mul_nonneg hK.le (hh₀ x)
    nlinarith
  · have hn := mul_nonneg hα.le (hf₀ x)
    nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_projection_two_relative_bounds
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (P : X → AlgebraProjection M)
    (hmass : Integrable (fun t => ‖(P t).val.val ξ‖^2+‖(P t).val.val η‖^2) μ)
    (hξ : Integrable (fun t => ‖centralVectorDefect J ξ (P t).val.val‖^2) μ)
    (hη : Integrable (fun t => ‖centralVectorDefect J η (P t).val.val‖^2) μ)
    {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hmean : α*(∫ t, ‖(P t).val.val ξ‖^2+‖(P t).val.val η‖^2 ∂μ)+
      K*(∫ t, ‖centralVectorDefect J ξ (P t).val.val‖^2 ∂μ) <
        α*K*(∫ t, ‖centralVectorDefect J η (P t).val.val‖^2 ∂μ)) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val ξ‖^2+‖p.val.val η‖^2 < K*‖centralVectorDefect J η p.val.val‖^2 ∧
      ‖centralVectorDefect J ξ p.val.val‖^2 < α*‖centralVectorDefect J η p.val.val‖^2 := by
  obtain ⟨t,ht⟩ := exists_two_relative_bounds _ _ _ hmass hη hξ
    (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) (fun _ => sq_nonneg _)
    hα hK hmean
  exact ⟨P t,ht⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateOutwardCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Two-vector projection cuts in the original algebra -/

namespace KadisonKastler

open MeasureTheory Finset Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem conjugationOperator_finiteOutward (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) :
    conjugationOperator J (finiteOutwardProjection P c t)=
      finiteOutwardProjection (fun i => conjugationOperator J (P i)) c t := by
  unfold finiteOutwardProjection
  split
  · rw [conjugationOperator_sub,conjugationOperator_one J hJ,conjugationOperator_finiteThreshold]
  · exact conjugationOperator_finiteThreshold J P _ t

theorem centralVectorDefect_projection (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (p : AlgebraProjection M) :
    centralVectorDefect J ξ p.val.val=(p.val.val-conjugationOperator J p.val.val) ξ := by
  rw [centralVectorDefect_apply,
    show star p.val.val=p.val.val from congrArg Subtype.val p.property.isSelfAdjoint.star_eq]
  rfl

theorem exists_finite_two_vector_projection_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (P : ι → AlgebraProjection M)
    (ho : ∀ i j, i ≠ j → (P i).val*(P j).val=0)
    (ht : ∑ i, (P i).val=1) (c : ι → ℝ)
    (ξ η : H) (hξ : J ξ=ξ) {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hsmall : α*(‖(∑ i, (c i : ℂ) • (P i).val.val) ξ‖^2+
      ‖(∑ i, (c i : ℂ) • (P i).val.val) η‖^2)+
      2*K*‖(∑ i, (c i : ℂ) • (P i).val.val) ξ‖*
        ‖((∑ i, (c i : ℂ) • (P i).val.val)-
          conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) ξ‖ <
      α*K/2*‖((∑ i, (c i : ℂ) • (P i).val.val)-
        conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) η‖^2) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val ξ‖^2+‖p.val.val η‖^2 < K*‖centralVectorDefect J η p.val.val‖^2 ∧
      ‖centralVectorDefect J ξ p.val.val‖^2 < α*‖centralVectorDefect J η p.val.val‖^2 := by
  let A : ι → H →L[ℂ] H := fun i => (P i).val.val
  let B : ι → H →L[ℂ] H := fun i => conjugationOperator J (A i)
  let S : H →L[ℂ] H := ∑ i, (c i : ℂ) • A i
  let p := finiteAlgebraOutwardProjection P ho c
  have hA (i : ι) : IsStarProjection (A i) :=
    (P i).property.map M.toStarSubalgebra.subtype
  have hB (i : ι) : IsStarProjection (B i) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright (P i)).property.map
      M.commutant.toStarSubalgebra.subtype
  have hAo (i j : ι) (hij : i ≠ j) : A i*A j=0 := congrArg Subtype.val (ho i j hij)
  have hBo (i j : ι) (hij : i ≠ j) : B i*B j=0 := by
    change conjugationOperator J (A i)*conjugationOperator J (A j)=0
    rw [← conjugationOperator_mul J hJ,hAo i j hij]
    ext ζ
    simp only [conjugationOperator_apply,zero_apply,map_zero]
  have hAt : ∑ i, A i=1 := by
    have he := congrArg M.toStarSubalgebra.subtype ht
    simp only [map_sum,map_one] at he
    change (∑ i, A i)=1 at he
    exact he
  have hBt : ∑ i, B i=1 := by
    have he := congrArg (conjugationOperator J) hAt
    rw [conjugationOperator_finsetSum,conjugationOperator_one J hJ] at he
    exact he
  have hc (i j : ι) : Commute (A i) (B j) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (P j).val) (A i) (P i).val.property
  have hsum : (∑ i, (c i : ℂ) • B i)=conjugationOperator J S :=
    (conjugationOperator_real_sum J A c).symm
  have hgap (ζ : H) (t : ℝ) :
      ‖centralVectorDefect J ζ (p t).val.val‖^2=
        ‖(finiteOutwardProjection A c t-finiteOutwardProjection B c t) ζ‖^2 := by
    rw [centralVectorDefect_projection]
    change ‖(finiteOutwardProjection A c t-
      conjugationOperator J (finiteOutwardProjection A c t)) ζ‖^2=_
    rw [conjugationOperator_finiteOutward J hJ]
  have hi (ζ : H) : Integrable (fun t => ‖centralVectorDefect J ζ (p t).val.val‖^2) := by
    simp_rw [hgap]
    exact finiteOutwardProjection_gap_integrable A B hA hB hAo hBo hAt hBt hc c c ζ
  have hm (ζ : H) : Integrable (fun t => ‖(p t).val.val ζ‖^2) :=
    finiteOutwardProjection_mass_integrable A hA hAo hAt c ζ
  have hmval (ζ : H) : (∫ t, ‖(p t).val.val ζ‖^2)=‖S ζ‖^2 :=
    finiteOutwardProjection_integral_mass A hA hAo hAt c ζ
  have hlo : ‖(S-conjugationOperator J S) η‖^2 ≤
      2*(∫ t, ‖centralVectorDefect J η (p t).val.val‖^2) := by
    simp_rw [hgap]
    have he := finiteOutwardProjection_integral_lower A B hA hB hAo hBo hAt hBt hc c c η
    rwa [hsum] at he
  have hup : (∫ t, ‖centralVectorDefect J ξ (p t).val.val‖^2) ≤
      2*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖ := by
    have he := finiteOutwardProjection_integral_upper_sq A B hA hB hAo hBo hAt hBt hc c c ξ
    rw [hsum] at he
    have hnorm : ‖conjugationOperator J S ξ‖=‖S ξ‖ := by
      simp only [conjugationOperator_apply,hξ,J.norm_map]
    rw [hnorm] at he
    apply (sq_le_sq₀ (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)).mp
    simp_rw [hgap]
    calc
      _ ≤ _ := he
      _ = (2*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖)^2 := by ring
  apply exists_projection_two_relative_bounds J ξ η p ((hm ξ).add (hm η)) (hi ξ) (hi η) hα hK
  rw [integral_add (hm ξ) (hm η),hmval ξ,hmval η]
  change α*(‖S ξ‖^2+‖S η‖^2)+2*K*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖ <
    α*K/2*‖(S-conjugationOperator J S) η‖^2 at hsmall
  calc
    _ ≤ α*(‖S ξ‖^2+‖S η‖^2)+K*(2*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hup hK.le)
    _ < α*K/2*‖(S-conjugationOperator J S) η‖^2 := by nlinarith [hsmall]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlo (mul_nonneg hα.le hK.le)]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_finite_two_vector_projection_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_finite_two_vector_projection_oai.{u_1, u_2}
