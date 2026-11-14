-- Prove2me | solution 1 for OAI.KadisonKastler.clippedGraphRow_error_le_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:56:30.659448+00:00
-- url     : https://prove2.me/submissions/63392b21-b7ad-4cba-8631-f33962152efa

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.Logic.Equiv.Prod
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
import Definitions.Def_Q260K031

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Norm clipping with preserved support and quotient image

The cutoff multiplies an element on the right by a continuous function of
its absolute value. Both the clipped part and the discarded part have
star squares bounded by the original star square.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

theorem clippingFunction_nonneg {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    0 ≤ clippingFunction β t :=
  div_nonneg hβ.le (hβ.le.trans (le_max_left β t))

theorem clippingFunction_le_one {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    clippingFunction β t ≤ 1 :=
  (div_le_one (hβ.trans_le (le_max_left β t))).mpr (le_max_left β t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourthMomentClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth-moment control of the clipping error

The continuous cutoff already used for quotient lifts also supplies the
tracial tail estimate needed to test bimodular operators on bounded balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

theorem discardedFunction_square_le_fourth {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * (1 - clippingFunction β t)) ^ 2 ≤ t ^ 4 / β ^ 2 := by
  rw [mul_sub, mul_one, mul_clippingFunction hβ]
  by_cases htβ : t ≤ β
  · rw [min_eq_left htβ, sub_self, zero_pow (by decide)]
    exact div_nonneg (pow_nonneg ht _) (sq_nonneg β)
  · have hβt : β ≤ t := (lt_of_not_ge htβ).le
    rw [min_eq_right hβt]
    apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
    have hprod : β * (t - β) ≤ t * t :=
      mul_le_mul hβt (sub_le_self t hβ.le) (sub_nonneg.mpr hβt) ht
    have hs := (sq_le_sq₀ (mul_nonneg hβ.le (sub_nonneg.mpr hβt))
      (mul_nonneg ht ht)).mpr hprod
    nlinarith only [hs]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The discarded square is bounded by the fourth power divided by the
square of the cutoff, in the C*-algebra order. -/
theorem spectralClip_discard_fourth_bound {β : ℝ} (hβ : 0 < β) (x : A) :
    star (x - spectralClip β x) * (x - spectralClip β x) ≤
      (β ^ 2)⁻¹ • (star x * x) ^ 2 := by
  have hcut : x - spectralClip β x =
      x * cfc (fun t => 1 - clippingFunction β t) (CFC.abs x) := by
    rw [cfc_sub (fun _ : ℝ => 1) (clippingFunction β) _ (by fun_prop)
      (clippingFunction_continuous hβ).continuousOn, cfc_const_one ℝ (CFC.abs x),
      mul_sub, mul_one]
    rfl
  have hfour : cfc (fun t : ℝ => t ^ 4) (CFC.abs x) = (star x * x) ^ 2 := by
    rw [cfc_pow_id (R := ℝ) (CFC.abs x) 4 (CFC.abs_nonneg x).isSelfAdjoint]
    calc
      CFC.abs x ^ 4 = (CFC.abs x ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (star x * x) ^ 2 := by rw [pow_two (CFC.abs x), CFC.abs_mul_abs]
  have hright : cfc (fun t : ℝ => t ^ 4 / β ^ 2) (CFC.abs x) =
      (β ^ 2)⁻¹ • (star x * x) ^ 2 := by
    simp_rw [div_eq_mul_inv, mul_comm (_ ^ 4)]
    rw [cfc_const_mul _ (fun t : ℝ => t ^ 4) _ (by fun_prop), hfour]
  rw [hcut, star_mul_cfc_abs x (fun t : ℝ => 1 - clippingFunction β t)
    (continuous_const.sub (clippingFunction_continuous hβ)), ← hright]
  apply (cfc_le_iff _ _ _
    ((continuous_id.mul (continuous_const.sub (clippingFunction_continuous hβ))).pow 2).continuousOn
    (by fun_prop)).mpr
  intro t ht
  exact discardedFunction_square_le_fourth hβ
    (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedPairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Extracting the scalar commutator from randomized rows

Finite Cauchy–Schwarz bounds the two row errors without a factor for the
number of random choices. Together with the scalar commutator estimate
this gives the constant 141 in the amplification argument.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators Topology

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
theorem finiteRMS_nonneg (v : Ω → H) : 0 ≤ finiteRMS v := Real.sqrt_nonneg _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedRMS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Elementary norm bounds for finite random vectors -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- Pointwise norm domination passes through finite root mean squares. -/
theorem finiteRMS_mono (v w : Ω → H) (hv : ∀ i, ‖v i‖ ≤ ‖w i‖) :
    finiteRMS v ≤ finiteRMS w := by
  apply Real.sqrt_le_sqrt
  exact expect_le_expect (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)

omit [InnerProductSpace ℂ H] in
/-- Squaring finite root mean square recovers its average of squares. -/
theorem finiteRMS_sq (v : Ω → H) :
    (finiteRMS v) ^ 2 = 𝔼 i, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg (fun _ _ => sq_nonneg _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorStateFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nontracial fourth moments of independent signs

The three-pairing sign identity holds for the actual vector functional.
The crossed pairing is bounded after summing the two orders of its
indices. This avoids applying a tracial fourth-moment theorem to the
nontracial vector state in the modular graph argument.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity of the vector functional is a Hilbert norm identity. -/
theorem realVectorState_star_mul_self (Ω : H) (x : H →L[ℂ] H) :
    realVectorState Ω (star x * x) = ‖x Ω‖ ^ 2 := by
  simp only [realVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The defining weighted graph norm, with no restriction on the scale. -/
theorem norm_rescaledGraphVector_sq (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c x‖ ^ 2 = ‖x Ω‖ ^ 2 + c ^ 2 * ‖star x Ω‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, rescaledGraphVector_zero, rescaledGraphVector_one,
    norm_smul, J.norm_map, Real.norm_eq_abs, mul_pow, sq_abs]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral clipping of a rescaled graph vector

The positive vector state can be applied to the two C*-order tail
bounds. Adjoint compatibility gives the same cutoff on both graph
coordinates. No traciality of the vector state is used.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.graphClippingOrder
attribute [local instance] OAI.KadisonKastler.graphClippingStarOrder
/-- A positive vector functional is monotone in the C*-order. -/
theorem realVectorState_mono (Ω : H) {x y : H →L[ℂ] H} (hxy : x ≤ y) :
    realVectorState Ω x ≤ realVectorState Ω y := by
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
  have h : 0 ≤ realVectorState Ω (star z * z) := by
    rw [realVectorState_star_mul_self]
    positivity
  rw [← hz, map_sub] at h
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphRowClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A common spectral cutoff for a replicated graph row

The cutoff acts on the left square of the entire row. Its norm is bounded
independently of the number of columns, while its normalized graph error
is controlled by the two fourth-moment sums in `graphRowCost`.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {I : Type*} [Fintype I]

attribute [local instance] OAI.KadisonKastler.graphRowClipOrder
attribute [local instance] OAI.KadisonKastler.graphRowClipStarOrder
theorem graphRowSquare_nonneg (Y : I → H →L[ℂ] H) : 0 ≤ graphRowSquare Y := by
  apply Finset.sum_nonneg
  intro i _
  simpa only [star_star] using star_mul_self_nonneg (star (Y i))

private theorem graphRowClipFactor_selfadjoint (β : ℝ) (Y : I → H →L[ℂ] H) :
    IsSelfAdjoint (graphRowClipFactor β Y) :=
  cfc_predicate (clippingFunction β) (CFC.sqrt (graphRowSquare Y))

private theorem clipping_remainder_sq_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (1 - clippingFunction β t) ^ 2 ≤ t ^ 2 / β ^ 2 := by
  have hf0 := clippingFunction_nonneg hβ t
  have hf1 := clippingFunction_le_one hβ t
  have hle : 1 - clippingFunction β t ≤ t / β := by
    by_cases h : t ≤ β
    · simp only [clippingFunction, max_eq_left h, div_self (ne_of_gt hβ), sub_self]
      exact div_nonneg ht hβ.le
    · have hb : β ≤ t := (lt_of_not_ge h).le
      have hr : 1 ≤ t / β := (le_div_iff₀ hβ).mpr (by simpa using hb)
      linarith
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - clippingFunction β t) hle 2
  simpa only [div_pow] using hsq

private theorem rowClip_remainder_sq_le {β : ℝ} (hβ : 0 < β)
    (Y : I → H →L[ℂ] H) :
    (1 - graphRowClipFactor β Y) ^ 2 ≤ (β ^ 2)⁻¹ • graphRowSquare Y := by
  let S := CFC.sqrt (graphRowSquare Y)
  have hS : 0 ≤ S := CFC.sqrt_nonneg _
  have hq : 1 - graphRowClipFactor β Y = cfc (fun t => 1 - clippingFunction β t) S := by
    rw [cfc_sub _ _ S (by fun_prop) (clippingFunction_continuous hβ).continuousOn,
      cfc_const_one ℝ S hS.isSelfAdjoint]
    rfl
  have hSS : S ^ 2 = graphRowSquare Y := by
    rw [pow_two]
    exact CFC.sqrt_mul_sqrt_self _ (graphRowSquare_nonneg Y)
  have hr : (β ^ 2)⁻¹ • graphRowSquare Y = cfc (fun t : ℝ => t ^ 2 / β ^ 2) S := by
    simp_rw [div_eq_mul_inv, mul_comm (_ ^ 2)]
    rw [cfc_const_mul _ _ S (by fun_prop), cfc_pow_id (R := ℝ) S 2 hS.isSelfAdjoint,
      hSS]
  have hcont : Continuous (fun t : ℝ => 1 - clippingFunction β t) :=
    continuous_const.sub (clippingFunction_continuous hβ)
  rw [hq, ← cfc_pow _ 2 _ hcont.continuousOn, hr]
  apply (cfc_le_iff _ _ _ (hcont.pow 2).continuousOn (by fun_prop)).mpr
  intro t ht
  exact clipping_remainder_sq_le hβ (spectrum_nonneg_of_nonneg hS ht)

private theorem rowClip_remainder_sandwich_le {β : ℝ} (hβ : 0 < β)
    (Y : I → H →L[ℂ] H) :
    (1 - graphRowClipFactor β Y) * graphRowSquare Y * (1 - graphRowClipFactor β Y) ≤
      (β ^ 2)⁻¹ • (graphRowSquare Y) ^ 2 := by
  let S := CFC.sqrt (graphRowSquare Y)
  have hS : 0 ≤ S := CFC.sqrt_nonneg _
  have he : S - spectralClip β S = S * (1 - graphRowClipFactor β Y) := by
    simp only [spectralClip, CFC.abs_of_nonneg S hS, mul_sub, mul_one]
    rfl
  have h := spectralClip_discard_fourth_bound hβ S
  rw [he, star_mul, star_sub, star_one, (graphRowClipFactor_selfadjoint β Y).star_eq,
    hS.isSelfAdjoint.star_eq] at h
  have hSS : S * S = graphRowSquare Y := CFC.sqrt_mul_sqrt_self _ (graphRowSquare_nonneg Y)
  simpa only [mul_assoc, ← hSS] using h

/-- The squared normalized rescaled-graph error of the single row cutoff
is at most its moment cost divided by the cutoff squared. -/
theorem clippedGraphRow_graph_error_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {β : ℝ} (hβ : 0 < β)
    (Y : Fin k → H →L[ℂ] H) :
    (𝔼 i, ‖rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
      (Y i - clippedGraphRow β Y i)‖ ^ 2) ≤ graphRowCost Ω Y / β ^ 2 := by
  let Q := 1 - graphRowClipFactor β Y
  have hQ : IsSelfAdjoint Q :=
    (IsSelfAdjoint.one (H →L[ℂ] H)).sub (graphRowClipFactor_selfadjoint β Y)
  have hdiff (i : Fin k) : Y i - clippedGraphRow β Y i = Q * Y i := by
    simp only [Q, clippedGraphRow, sub_mul, one_mul]
  have hright (i : Fin k) :
      ‖(Q * Y i) Ω‖ ^ 2 ≤ (β ^ 2)⁻¹ *
        realVectorState Ω (star (Y i) * graphRowSquare Y * Y i) := by
    have h := star_left_conjugate_le_conjugate (rowClip_remainder_sq_le hβ Y) (Y i)
    have hφ := realVectorState_mono Ω h
    have he : star (Y i) * (1 - graphRowClipFactor β Y) ^ 2 * Y i =
        star (Q * Y i) * (Q * Y i) := by
      change star (Y i) * Q ^ 2 * Y i = _
      simp only [pow_two, star_mul, hQ.star_eq, mul_assoc]
    rw [he, realVectorState_star_mul_self] at hφ
    simpa only [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul] using hφ
  have hleft : (∑ i, ‖star (Q * Y i) Ω‖ ^ 2) ≤
      (β ^ 2)⁻¹ * realVectorState Ω ((graphRowSquare Y) ^ 2) := by
    have h := realVectorState_mono Ω (rowClip_remainder_sandwich_le hβ Y)
    have he : (∑ i, ‖star (Q * Y i) Ω‖ ^ 2) =
        realVectorState Ω (Q * graphRowSquare Y * Q) := by
      simp only [graphRowSquare, Finset.mul_sum, Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hp : Q * (Y i * star (Y i)) * Q = star (star (Q * Y i)) * star (Q * Y i) := by
        simp only [star_mul, star_star, hQ.star_eq, mul_assoc]
      rw [hp, realVectorState_star_mul_self]
    rw [he]
    simpa only [map_smul, smul_eq_mul] using h
  simp_rw [hdiff, norm_rescaledGraphVector_sq, Real.sq_sqrt (Nat.cast_nonneg k)]
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_add_distrib, ← Finset.mul_sum,
    Fintype.card_fin]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hright i)
  rw [← Finset.mul_sum] at hs
  unfold graphRowCost
  simp only [Fintype.card_fin]
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hb := add_le_add hs (mul_le_mul_of_nonneg_left hleft hkR.le)
  have hd := div_le_div_of_nonneg_right hb hkR.le
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FlattenedGraphRow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded replicated row retaining the graph signal

A single cutoff of the row square preserves algebra membership and loses
at most one thirty-second of the graph signal in normalized mean square.
The cutoff and the row norm are independent of the row length.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.flattenedRowOrder
local instance flattenedRowStarOrder_r667467_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- The common row cutoff has small graph error at the fixed cutoff. -/
theorem clippedGraphRow_error_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (Y : Fin k → H →L[ℂ] H)
    (hcost : graphRowCost Ω Y ≤ 16777216) :
    finiteRMS (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
      (Y i - clippedGraphRow 131072 Y i)) ≤ 1 / 32 := by
  have h := clippedGraphRow_graph_error_le hk J Ω (by norm_num : (0 : ℝ) < 131072) Y
  rw [← finiteRMS_sq] at h
  have hc := h.trans (div_le_div_of_nonneg_right hcost (by norm_num))
  nlinarith [finiteRMS_nonneg (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
    (Y i - clippedGraphRow 131072 Y i))]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform row flattening at arbitrary large rescalings

Rounding the squared rescaling up changes the moment normalization by at
most a factor two. The same fixed row cutoff remains sufficient.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]


/-- Increasing the square of the graph scale increases its norm. -/
theorem norm_rescaledGraphVector_mono_square
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c b : ℝ} (hcb : c ^ 2 ≤ b ^ 2)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c x‖ ≤ ‖rescaledGraphVector J Ω b x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_rescaledGraphVector_sq, norm_rescaledGraphVector_sq]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcb (sq_nonneg _))

/-- At a scale whose square is at most the row length, the same cutoff
has the same normalized graph error bound. -/
theorem clippedGraphRow_error_le_scale_oai {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c : ℝ} (hc : c ^ 2 ≤ (k : ℝ))
    (Y : Fin k → H →L[ℂ] H) (hcost : graphRowCost Ω Y ≤ 16777216) :
    finiteRMS (fun i => rescaledGraphVector J Ω c
      (Y i - clippedGraphRow 131072 Y i)) ≤ 1 / 32 := by
  apply (finiteRMS_mono _ _ ?_).trans (clippedGraphRow_error_le hk J Ω Y hcost)
  intro i
  apply norm_rescaledGraphVector_mono_square J Ω
  simpa only [Real.sq_sqrt (Nat.cast_nonneg k)] using hc

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.clippedGraphRow_error_le_scale_oai.{u_1} := @OAI.KadisonKastler.clippedGraphRow_error_le_scale_oai.{u_1}
