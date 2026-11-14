-- Prove2me | solution 1 for OAI.KadisonKastler.constructed_exists_normalizer_near_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:51:47.918845+00:00
-- url     : https://prove2.me/submissions/ef1ee9c5-d559-41d1-8961-019157757c6d

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.Analysis.Normed.Algebra.Exponential
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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
import Mathlib.Topology.MetricSpace.Contracting
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K068

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

namespace BimoduleMean

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)

/-- The linear terms cancel exactly in the centered product. -/
theorem covariance (x y : A) :
    m.toCLM (x * y) - m.toCLM x * m.toCLM y =
      m.toCLM ((x - ι (m.toCLM x)) * (y - ι (m.toCLM y))) := by
  simp only [sub_mul, mul_sub, map_sub, m.map_right, m.map_left, m.fixed]
  noncomm_ring

/-- Contractivity of the mean bounds the covariance by its two residuals. -/
theorem norm_covariance_le (x y : A) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤
      ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := by
  rw [m.covariance]
  exact (m.norm_le _).trans (norm_mul_le _ _)

/-- For a unitary the covariance identity is the exact unitarity defect. -/
theorem variance (x : unitary A) :
    1 - star (m.toCLM (x : A)) * m.toCLM (x : A) =
      m.toCLM (star ((x : A) - ι (m.toCLM (x : A))) *
        ((x : A) - ι (m.toCLM (x : A)))) := by
  have hc := m.covariance (star (x : A)) (x : A)
  have hi : ι (m.toCLM (star (x : A))) = star (ι (m.toCLM (x : A))) := by
    rw [m.map_star]
    exact StarHomClass.map_star ι _
  rw [hi] at hc
  simpa only [Unitary.star_mul_self_of_mem x.property, m.map_one, m.map_star,
    star_sub] using hc

/-- Averaging preserves the error from a field independent of the mean variable. -/
theorem norm_sub_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖m.toCLM x - b‖ ≤ e := by
  rw [← m.fixed b, ← map_sub]
  exact (m.norm_le _).trans h

/-- The residual from the average is at most twice the original error. -/
theorem norm_residual_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖x - ι (m.toCLM x)‖ ≤ 2 * e := by
  calc
    _ ≤ ‖x - ι b‖ + ‖ι b - ι (m.toCLM x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ e + e := add_le_add h (by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le ι _).trans
        (by simpa only [norm_sub_rev] using m.norm_sub_le x b h))
    _ = _ := by ring

/-- Two residuals bounded by `2e` give the quadratic covariance bound. -/
theorem norm_covariance_le_four_mul_sq (x y : A) {e : ℝ} (he : 0 ≤ e)
    (hx : ‖x - ι (m.toCLM x)‖ ≤ 2 * e)
    (hy : ‖y - ι (m.toCLM y)‖ ≤ 2 * e) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤ 4 * e ^ 2 := by
  calc
    _ ≤ ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := m.norm_covariance_le x y
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The average of a unitary within `e` of the fixed algebra has unitarity
error at most `4e²`. -/
theorem norm_variance_le_four_mul_sq (x : unitary A) (b : B) {e : ℝ}
    (he : 0 ≤ e) (hx : ‖(x : A) - ι b‖ ≤ e) :
    ‖1 - star (m.toCLM (x : A)) * m.toCLM (x : A)‖ ≤ 4 * e ^ 2 := by
  have hr := m.norm_residual_le (x : A) b hx
  rw [m.variance]
  calc
    _ ≤ ‖star ((x : A) - ι (m.toCLM (x : A))) *
        ((x : A) - ι (m.toCLM (x : A)))‖ := m.norm_le _
    _ ≤ ‖(x : A) - ι (m.toCLM (x : A))‖ *
        ‖(x : A) - ι (m.toCLM (x : A))‖ := by
      simpa only [norm_star] using norm_mul_le
        (star ((x : A) - ι (m.toCLM (x : A))))
        ((x : A) - ι (m.toCLM (x : A)))
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hr hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

end BimoduleMean

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

/-- Polar normalization costs no more than the unitarity defect. -/
theorem exists_polar_unitary_close_of_near_unitary (x : B) (v : unitary B)
    (hx : ‖x - (v : B)‖ < 1) :
    ∃ u : unitary B, (u : B) * CFC.abs x = x ∧
      ‖(u : B) - x‖ ≤ ‖star x * x - 1‖ := by
  nontriviality B
  have hinv : ‖(((Unitary.toUnits v)⁻¹ : Bˣ) : B)‖ = 1 := by
    change ‖star (v : B)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  let t : Bˣ := Units.ofNearby (Unitary.toUnits v) x (by
    simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hx)
  have ht : (t : B) = x := rfl
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  rw [ht] at hu
  refine ⟨u, hu, ?_⟩
  have hid : (u : B) - x = (u : B) * (1 - CFC.abs x) := by
    rw [mul_sub, mul_one, hu]
  rw [hid, CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact norm_sqrt_sub_one_le (star x * x) (star_mul_self_nonneg x)

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Normalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Published small-normalizer factorization and its consequence

The factorization hypothesis is Proposition 3.2 of
Cameron–Christensen–Sinclair–Smith–White–Wiggins, *Kadison–Kastler stable
factors*, Duke Math. J. 163 (2014), 2639–2686.  That proposition factors
two sufficiently close normalizers through the algebra and its commutant.

Its specialization at the identity gives the small exact normalizer lemma
used in §7 of *Universal strong Kadison–Kastler stability* (2026), with
radius one and displacement constant four, under the stated factorization
hypothesis.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unitaries belonging to the algebra normalize it. -/
theorem conjugates_self_of_mem {P : VonNeumannAlgebra H}
    {a : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P) :
    Conjugates a P P := by
  change unitaryConj a '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem ha hx) (star_mem ha)
  · intro hy
    refine ⟨unitaryConj (star a) y, ?_, ?_⟩
    · exact mul_mem (mul_mem (star_mem ha) hy)
        (by simpa only [Unitary.coe_star, star_star] using ha)
    · simpa only [star_star] using unitaryConj_star_unitaryConj (star a) y

/-- Unitaries in the commutant act trivially on the algebra by conjugation. -/
theorem unitaryConj_eq_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant)
    {x : H →L[ℂ] H} (hx : x ∈ P) : unitaryConj b x = x := by
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  rw [unitaryConj, ← hcomm, mul_assoc,
    Unitary.mul_star_self_of_mem b.property, mul_one]

theorem conjugates_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant) :
    Conjugates b P P := by
  change unitaryConj b '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [unitaryConj_eq_self_of_mem_commutant hb hy] using hy
  · intro hx
    exact ⟨x, hx, unitaryConj_eq_self_of_mem_commutant hb hx⟩

/-- A product of an algebra unitary and a commutant unitary normalizes the algebra. -/
theorem conjugates_self_of_separate_factors {P : VonNeumannAlgebra H}
    {a b : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P)
    (hb : (b : H →L[ℂ] H) ∈ P.commutant) : Conjugates (a * b) P P :=
  (conjugates_self_of_mem_commutant hb).trans (conjugates_self_of_mem ha)

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedNormalizerAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.operatorFieldFamilyCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.restrictedOperatorFamilyCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging close exact normalizers within the normalizer group

Separate the near-identity residual into its algebra and commutant
factors, average these separately, and take their polar unitaries inside
the respective algebras. The quadratic covariance estimate controls the
loss from separating the average of the product.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.constructedNormalizerAverageOrder
local instance constructedNormalizerAverageStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The polar correction is taken inside the given algebra. -/
theorem constructed_exists_polar_unitary_mem_of_near_one (P : VonNeumannAlgebra H)
    (x : H →L[ℂ] H) (hx : x ∈ P) (hnear : ‖x - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ P ∧
      ‖(u : H →L[ℂ] H) - x‖ ≤ ‖star x * x - 1‖ := by
  let a : Algebra P := ⟨x, hx⟩
  obtain ⟨u, -, hn⟩ := exists_polar_unitary_close_of_near_unitary a 1 hnear
  let v := Unitary.map (StarMonoidHom.ofClass P.toStarSubalgebra.subtype) u
  exact ⟨v, (u : Algebra P).property, hn⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

attribute [local instance] OAI.KadisonKastler.constructedNormalizerAverageFamilyCStar
omit [Group G] in
/-- A contractive bimodule mean that preserves the two concrete algebras
replaces a close family of normalizers by a normalizer at quadratic cost. -/
theorem constructed_exists_normalizer_near_mean_oai
    (P : VonNeumannAlgebra H) (hpub : SmallNormalizerFactorization P)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hpres : ∀ (Q : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H)),
      (∀ g, F g ∈ Q) → m.toCLM F ∈ Q)
    (X : unitary (G →ᵇ (H →L[ℂ] H)))
    (hX : ∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) X g) P P)
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates v P P)
    {e : ℝ} (he : 0 ≤ e) (heSmall : 64 * e < 1)
    (hclose : ∀ g, ‖X.val g - (v : H →L[ℂ] H)‖ ≤ e) :
    ∃ w : unitary (H →L[ℂ] H), Conjugates w P P ∧
      ‖(w : H →L[ℂ] H) - m.toCLM X.val‖ ≤ 1200 * e ^ 2 := by
  let residual (g : G) := unitaryFamilyEval (B := H →L[ℂ] H) X g * star v
  have hrNorm (g : G) : ‖(residual g : H →L[ℂ] H) - 1‖ ≤ e := by
    have hid : (residual g : H →L[ℂ] H) - 1 =
        (X.val g - (v : H →L[ℂ] H)) * star (v : H →L[ℂ] H) := by
      change X.val g * star (v : H →L[ℂ] H) - 1 = _
      rw [sub_mul, Unitary.mul_star_self_of_mem v.property]
    rw [hid, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    exact hclose g
  have hr (g : G) : ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      residual g = a * b ∧
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤ 10 * e := by
    obtain ⟨a, b, ha, hb, hab, hn⟩ := hpub (residual g)
      (hv.symm.trans (hX g)) ((hrNorm g).trans_lt (by linarith))
    exact ⟨a, b, ha, hb, hab, hn.trans (mul_le_mul_of_nonneg_left (hrNorm g) (by norm_num))⟩
  choose a b ha hb hab hn using hr
  let A := boundedUnitaryFamily a
  let B := boundedUnitaryFamily b
  have hA : ‖A.val - boundaryConstant (G := G) (1 : H →L[ℂ] H)‖ ≤ 10 * e := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro g
    have h := hn g
    change ‖(a g : H →L[ℂ] H) - 1‖ ≤ _
    linarith [norm_nonneg ((b g : H →L[ℂ] H) - 1)]
  have hB : ‖B.val - boundaryConstant (G := G) (1 : H →L[ℂ] H)‖ ≤ 10 * e := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro g
    have h := hn g
    change ‖(b g : H →L[ℂ] H) - 1‖ ≤ _
    linarith [norm_nonneg ((a g : H →L[ℂ] H) - 1)]
  have hAmem : m.toCLM A.val ∈ P := hpres P A.val ha
  have hBmem : m.toCLM B.val ∈ P.commutant := hpres P.commutant B.val hb
  have hAnear : ‖m.toCLM A.val - 1‖ < 1 := (m.norm_sub_le A.val 1 hA).trans_lt (by linarith)
  have hBnear : ‖m.toCLM B.val - 1‖ < 1 := (m.norm_sub_le B.val 1 hB).trans_lt (by linarith)
  obtain ⟨p, hp, hpn⟩ := constructed_exists_polar_unitary_mem_of_near_one P _ hAmem hAnear
  obtain ⟨q, hq, hqn⟩ := constructed_exists_polar_unitary_mem_of_near_one P.commutant _ hBmem hBnear
  have hpBound : ‖(p : H →L[ℂ] H) - m.toCLM A.val‖ ≤ 400 * e ^ 2 := by
    have h := m.norm_variance_le_four_mul_sq A 1 (by positivity : 0 ≤ 10 * e) hA
    rw [norm_sub_rev] at h
    nlinarith [hpn]
  have hqBound : ‖(q : H →L[ℂ] H) - m.toCLM B.val‖ ≤ 400 * e ^ 2 := by
    have h := m.norm_variance_le_four_mul_sq B 1 (by positivity : 0 ≤ 10 * e) hB
    rw [norm_sub_rev] at h
    nlinarith [hqn]
  have hcov : ‖m.toCLM (A.val * B.val) - m.toCLM A.val * m.toCLM B.val‖ ≤
      400 * e ^ 2 := by
    have h := m.norm_covariance_le_four_mul_sq A.val B.val (by positivity : 0 ≤ 10 * e)
      (m.norm_residual_le A.val 1 hA) (m.norm_residual_le B.val 1 hB)
    nlinarith
  have hAnorm : ‖m.toCLM A.val‖ ≤ 1 := (m.norm_le _).trans (norm_unitary_le_one A)
  have hprod : ‖(p : H →L[ℂ] H) * (q : H →L[ℂ] H) -
      m.toCLM A.val * m.toCLM B.val‖ ≤ 800 * e ^ 2 := by
    have hid : (p : H →L[ℂ] H) * (q : H →L[ℂ] H) -
        m.toCLM A.val * m.toCLM B.val =
        ((p : H →L[ℂ] H) - m.toCLM A.val) * (q : H →L[ℂ] H) +
        m.toCLM A.val * ((q : H →L[ℂ] H) - m.toCLM B.val) := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖((p : H →L[ℂ] H) - m.toCLM A.val) * (q : H →L[ℂ] H)‖ +
          ‖m.toCLM A.val * ((q : H →L[ℂ] H) - m.toCLM B.val)‖ := norm_add_le _ _
      _ ≤ 400 * e ^ 2 + 400 * e ^ 2 := add_le_add
        (by simpa only [CStarRing.norm_mul_coe_unitary] using hpBound)
        ((norm_mul_le _ _).trans ((mul_le_mul hAnorm hqBound (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
      _ = _ := by ring
  have hfield : X.val = A.val * B.val * boundaryConstant (G := G) (v : H →L[ℂ] H) := by
    apply BoundedContinuousFunction.ext
    intro g
    have h := congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H)) (hab g)
    change X.val g * star (v : H →L[ℂ] H) = (a g : H →L[ℂ] H) * (b g : H →L[ℂ] H) at h
    change X.val g = (a g : H →L[ℂ] H) * (b g : H →L[ℂ] H) * (v : H →L[ℂ] H)
    rw [← h, mul_assoc, Unitary.star_mul_self_of_mem v.property, mul_one]
  refine ⟨p * q * v, hv.trans (conjugates_self_of_separate_factors hp hq), ?_⟩
  rw [hfield, m.map_right]
  change ‖((p : H →L[ℂ] H) * (q : H →L[ℂ] H)) * (v : H →L[ℂ] H) -
    m.toCLM (A.val * B.val) * (v : H →L[ℂ] H)‖ ≤ _
  rw [← sub_mul, CStarRing.norm_mul_coe_unitary]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hprod (by simpa only [norm_sub_rev] using hcov)).trans_eq (by ring))

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.constructed_exists_normalizer_near_mean_oai.{u_1, u_2} := @OAI.KadisonKastler.constructed_exists_normalizer_near_mean_oai.{u_1, u_2}
