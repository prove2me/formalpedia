-- Prove2me | solution 1 for OAI.KadisonKastler.exists_unitary_approx_of_nearInclusion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:45.049193+00:00
-- url     : https://prove2.me/submissions/6852e3a5-8dfb-4b09-b011-6f20e8752c89

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
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K029

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

private theorem boundary_sqrt_scalar_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  have hlarge : 1 ≤ (Real.sqrt t + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg t]
  calc
    _ ≤ (Real.sqrt t - 1) ^ 2 * (Real.sqrt t + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge (sq_nonneg (Real.sqrt t - 1))]
    _ = _ := by rw [← mul_pow]; congr 1; nlinarith [Real.sq_sqrt ht]

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- The square root cannot increase the operator-norm error from one. -/
theorem norm_sqrt_sub_one_le (a : B) (ha : 0 ≤ a) :
    ‖CFC.sqrt a - 1‖ ≤ ‖a - 1‖ := by
  let b := CFC.sqrt a
  have hb : star b = b := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have haStar : star a = a := ha.isSelfAdjoint.star_eq
  have hbCFC : b = cfc Real.sqrt a := by
    dsimp [b]
    rw [CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  have hleft : cfc (fun t : ℝ => (Real.sqrt t - 1) ^ 2) a =
      star (b - 1) * (b - 1) := by
    rw [cfc_pow (fun t : ℝ => Real.sqrt t - 1) 2 a,
      cfc_sub Real.sqrt (fun _ : ℝ => 1) a,
      cfc_const_one ℝ a, ← hbCFC, star_sub, hb, star_one, pow_two]
  have hright : cfc (fun t : ℝ => (t - 1) ^ 2) a =
      star (a - 1) * (a - 1) := by
    rw [cfc_pow (fun t : ℝ => t - 1) 2 a,
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) a,
      cfc_id' ℝ a, cfc_const_one ℝ a, star_sub, haStar, star_one, pow_two]
  have horder : star (b - 1) * (b - 1) ≤ star (a - 1) * (a - 1) := by
    rw [← hleft, ← hright]
    apply (cfc_le_iff _ _ a).mpr
    intro t ht
    exact boundary_sqrt_scalar_sub_one_sq_le (spectrum_nonneg_of_nonneg ha ht)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at hn
  change ‖b - 1‖ ≤ ‖a - 1‖
  nlinarith [norm_nonneg (b - 1), norm_nonneg (a - 1)]

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearInclusionDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing strict near-inclusion approximants -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- An algebra approximant can be normalized into its unit ball with at
most twice the original error. -/
theorem exists_unitBall_approx_of_algebra_approx
    {x y : H →L[ℂ] H} (hx : ‖x‖ ≤ 1) (hy : y ∈ N) :
    ∃ z ∈ unitBall N, ‖x - z‖ ≤ 2 * ‖x - y‖ := by
  by_cases hy1 : ‖y‖ ≤ 1
  · exact ⟨y, ⟨hy, hy1⟩, by nlinarith [norm_nonneg (x - y)]⟩
  have hypos : 0 < ‖y‖ := by linarith
  let z : H →L[ℂ] H := (‖y‖⁻¹ : ℂ) • y
  have hznorm : ‖z‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hypos)
  have hyz : ‖y - z‖ = ‖y‖ - 1 := by
    have hi : 0 ≤ 1 - ‖y‖⁻¹ := by
      have ht : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hypos).mpr (lt_of_not_ge hy1).le
      linarith
    have he : y - z = ((1 - ‖y‖⁻¹ : ℝ) : ℂ) • y := by
      simp only [z, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
        sub_smul, one_smul]
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hypos.ne']
  have hnorm : ‖y‖ - 1 ≤ ‖x - y‖ := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith
  refine ⟨z, ⟨N.toStarSubalgebra.smul_mem hy _, hznorm.le⟩, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub x y z).trans (by rw [hyz]; linarith)

/-- The published strict near-inclusion convention controls the closed
unit balls with the factor two from normalization. -/
theorem exists_unitBall_approx_of_nearInclusion {γ : ℝ}
    (h : NearInclusion M N γ) {x : H →L[ℂ] H} (hx : x ∈ unitBall M) :
    ∃ y ∈ unitBall N, ‖x - y‖ < 2 * γ := by
  obtain ⟨γ', hγ', happrox⟩ := h
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff ⟨0, zero_mem N⟩).mp
    ((happrox x hx).trans_lt hγ')
  obtain ⟨z, hz, hxz⟩ := exists_unitBall_approx_of_algebra_approx hx.2 hy
  have hxy' : ‖x - y‖ < γ := by simpa only [dist_eq_norm] using hxy
  exact ⟨z, hz, hxz.trans_lt (by linarith)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteNeighbor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finiteness of a nearby von Neumann algebra

A finite factor has unitary polar decompositions.  An isometry close to
its unit ball is therefore close to a unitary, hence invertible.  This
proves the finiteness part of the manuscript's finite-neighbor lemma.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The defect of a contraction near an isometry is at most twice its error. -/
theorem norm_isometry_defect_le {x v : A} (hx : ‖x‖ ≤ 1)
    (hv : star v * v = 1) :
    ‖star x * x - 1‖ ≤ 2 * ‖x - v‖ := by
  have hvn : ‖v‖ ≤ 1 := by
    have h := congrArg norm hv
    rw [CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : A)‖ ≤ 1 := norm_unitary_le_one (1 : unitary A)
    nlinarith [norm_nonneg v]
  have he : star x * x - 1 = star x * (x - v) + star (x - v) * v := by
    rw [star_sub, mul_sub, sub_mul, hv]
    noncomm_ring
  calc
    _ ≤ ‖star x * (x - v)‖ + ‖star (x - v) * v‖ := he ▸ norm_add_le _ _
    _ ≤ ‖x‖ * ‖x - v‖ + ‖x - v‖ * ‖v‖ := by
      simpa only [norm_star] using add_le_add
        (norm_mul_le (star x) (x - v)) (norm_mul_le (star (x - v)) v)
    _ ≤ 1 * ‖x - v‖ + ‖x - v‖ * 1 := add_le_add
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hvn (norm_nonneg _))
    _ = _ := by ring

/-- A unitary polar factor is close to its element by its isometry defect. -/
theorem norm_unitary_polar_sub_le (x : A) (u : unitary A)
    [PartialOrder A] [StarOrderedRing A]
    (hu : (u : A) * CFC.abs x = x) :
    ‖(u : A) - x‖ ≤ ‖star x * x - 1‖ := by
  have he : (u : A) - x = (u : A) * (1 - CFC.abs x) := by
    rw [mul_sub, mul_one, hu]
  rw [he, CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact norm_sqrt_sub_one_le _ (star_mul_self_nonneg _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ClosedUnitaryApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary approximation in a closed neighbouring algebra

Spectral permanence reflects invertibility of a sufficiently close contraction
into the closed subalgebra. Its polar unitary then has at most three times the
original approximation error. No finiteness assumption on the target is needed.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Invertibility near an ambient unitary is reflected into a closed
C-star subalgebra. -/
theorem isUnit_of_near_ambient_unitary (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (u : unitary A) (x : S)
    (hclose : ‖(x : A) - (u : A)‖ < 1) : IsUnit x := by
  apply S.coe_isUnit.mp
  nontriviality A
  have hinv : ‖(((Unitary.toUnits u)⁻¹ : Aˣ) : A)‖ = 1 := by
    change ‖star (u : A)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  exact (Units.ofNearby (Unitary.toUnits u) (x : A) (by
    simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hclose)).isUnit

/-- Polar normalization of a nearby contraction in an arbitrary closed
subalgebra costs a factor of three. -/
theorem exists_unitary_near_of_closed_subalgebra (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (u : unitary A) (x : S) (hx : ‖x‖ ≤ 1)
    (hclose : ‖(x : A) - (u : A)‖ < 1) :
    ∃ v : unitary S, ‖(v : A) - (u : A)‖ ≤ 3 * ‖(x : A) - (u : A)‖ := by
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  have hi := isUnit_of_near_ambient_unitary S u x hclose
  obtain ⟨v, hv⟩ := exists_unitary_mul_abs hi.unit
  rw [hi.unit_spec] at hv
  have hdefect : ‖star x * x - 1‖ ≤ 2 * ‖(x : A) - (u : A)‖ :=
    norm_isometry_defect_le (A := A) (x := (x : A)) hx u.property.1
  have hpolar := (norm_unitary_polar_sub_le x v hv).trans hdefect
  refine ⟨v, ?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub (v : A) (x : A) (u : A)
  change ‖(v : A) - (x : A)‖ ≤ _ at hpolar
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- Strict one-sided near inclusion also supplies unitary approximants.
The additional factor two normalizes the original algebra approximant. -/
theorem exists_unitary_approx_of_nearInclusion_oai {γ : ℝ}
    (hsmall : 2 * γ ≤ 1) (hnear : NearInclusion M N γ)
    (u : unitary (Algebra M)) :
    ∃ v : unitary (Algebra N),
      ‖(v : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ < 6 * γ := by
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra N
  obtain ⟨x, hx, hxu⟩ := exists_unitBall_approx_of_nearInclusion hnear
    (show (u : H →L[ℂ] H) ∈ unitBall M from
      ⟨(u : Algebra M).property, norm_unitary_le_one u⟩)
  have hclose : ‖x - (u : H →L[ℂ] H)‖ < 2 * γ := by
    simpa only [norm_sub_rev] using hxu
  obtain ⟨v, hv⟩ := exists_unitary_near_of_closed_subalgebra
    N.toStarSubalgebra (ambientAlgebraUnitary u) (⟨x, hx.1⟩ : Algebra N) hx.2
    (hclose.trans_le hsmall)
  exact ⟨v, hv.trans_lt (by change 3 * ‖x - (u : H →L[ℂ] H)‖ < _; linarith)⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_2} : type_of% @OAI.KadisonKastler.exists_unitary_approx_of_nearInclusion_oai.{u_2} := @OAI.KadisonKastler.exists_unitary_approx_of_nearInclusion_oai.{u_2}
