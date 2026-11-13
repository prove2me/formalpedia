-- Prove2me | solution 1 for OAI.KadisonKastler.opNorm_le_of_finite_covariance_families
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:18.190418+00:00
-- url     : https://prove2.me/submissions/b73c0b4d-4424-419a-a29d-148ecf2e5c7f

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K010
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem clippingFunction_square_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * clippingFunction β t) ^ 2 ≤ t ^ 2 := by
  have h0 := clippingFunction_nonneg hβ t
  have h1 := clippingFunction_le_one hβ t
  have ht0 : 0 ≤ t * clippingFunction β t := mul_nonneg ht h0
  have ht1 : t * clippingFunction β t ≤ t := by nlinarith
  nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Clipping does not increase the star square. -/
theorem spectralClip_star_mul_self_le {β : ℝ} (hβ : 0 < β) (x : A) :
    star (spectralClip β x) * spectralClip β x ≤ star x * x := by
  rw [spectralClip_star_mul_self hβ,
    ← CFC.abs_mul_abs x, ← pow_two, ← cfc_pow_id (R := ℝ) (CFC.abs x) 2]
  apply (cfc_le_iff _ _ _ (by exact
    ((continuous_id.mul (clippingFunction_continuous hβ)).pow 2).continuousOn)).mpr
  intro t ht
  exact clippingFunction_square_le hβ (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourthMomentClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A positive trace is monotone on selfadjoint elements. -/
theorem FaithfulTracialState.re_mono (τ : FaithfulTracialState A) {x y : A}
    (hxy : x ≤ y) : (τ.toLinearMap x).re ≤ (τ.toLinearMap y).re := by
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
  have h := τ.positive z
  rw [← hz, map_sub, Complex.sub_re] at h
  linarith

/-- Fourth moments control the squared tracial norm lost to clipping. -/
theorem traceTwoNorm_spectralClip_discard_sq_le
    (τ : FaithfulTracialState A) {β : ℝ} (hβ : 0 < β) (x : A) :
    traceTwoNorm τ (x - spectralClip β x) ^ 2 ≤
      (τ.toLinearMap ((star x * x) ^ 2)).re / β ^ 2 := by
  have h := τ.re_mono (spectralClip_discard_fourth_bound hβ x)
  rw [traceTwoNorm_sq]
  simpa only [LinearMap.map_smul_of_tower, Complex.smul_re,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem traceTwoNorm_spectralClip_le (τ : FaithfulTracialState A)
    {β : ℝ} (hβ : 0 < β) (x : A) :
    traceTwoNorm τ (spectralClip β x) ≤ traceTwoNorm τ x := by
  have h := τ.re_mono (spectralClip_star_mul_self_le hβ x)
  rw [← traceTwoNorm_sq, ← traceTwoNorm_sq] at h
  nlinarith [traceTwoNorm_nonneg τ (spectralClip β x), traceTwoNorm_nonneg τ x]

/-- A uniform fourth-moment bound gives the averaged squared tail bound. -/
theorem expect_traceTwoNorm_spectralClip_discard_sq_le
    {ι : Type*} [Fintype ι] (τ : FaithfulTracialState A) (x : ι → A)
    {β C : ℝ} (hβ : 0 < β)
    (hfour : (𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re) ≤ C) :
    (𝔼 i, traceTwoNorm τ (x i - spectralClip β (x i)) ^ 2) ≤ C / β ^ 2 := by
  calc
    _ ≤ 𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re / β ^ 2 :=
      Finset.expect_le_expect fun i _ => traceTwoNorm_spectralClip_discard_sq_le τ hβ (x i)
    _ = (𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re) / β ^ 2 :=
      (Finset.expect_div _ _ _).symm
    _ ≤ C / β ^ 2 := div_le_div_of_nonneg_right hfour (sq_nonneg β)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FinitePhases
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Finite phase randomization

Orthogonal scalar phases turn a coefficient column into a random vector
with exactly the same mean square. This is the finite Parseval identity
used for the randomized commutator coefficients in §3.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Ω W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W]

theorem finitePhaseSum_inner (χ : W → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t : Ω, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v u : W → H) :
    (𝔼 t : Ω, inner ℂ (finitePhaseSum χ v t) (finitePhaseSum χ u t)) =
      ∑ w, inner ℂ (v w) (u w) := by
  simp_rw [finitePhaseSum, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, ← mul_assoc, Finset.expect_sum_comm, ← Finset.expect_mul]
  calc
    _ = ∑ i : W, ∑ j : W, (if i = j then (1 : ℂ) else 0) *
        inner ℂ (v i) (u j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [hχ]
    _ = _ := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedPairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [InnerProductSpace ℂ H] in
theorem expect_norm_mul_le_finiteRMS (v w : Ω → H) :
    (𝔼 i, ‖v i‖ * ‖w i‖) ≤ finiteRMS v * finiteRMS w := by
  have hv : 0 ≤ (𝔼 i, ‖v i‖ ^ 2) := expect_nonneg (fun _ _ => sq_nonneg _)
  have hw : 0 ≤ (𝔼 i, ‖w i‖ ^ 2) := expect_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (expect_nonneg (fun _ _ => by positivity))
    (mul_nonneg (finiteRMS_nonneg v) (finiteRMS_nonneg w))).mp
  rw [mul_pow, finiteRMS, finiteRMS, Real.sq_sqrt hv, Real.sq_sqrt hw]
  exact expect_mul_sq_le_sq_mul_sq univ (fun i => ‖v i‖) (fun i => ‖w i‖)

/-- An average of arbitrary operator-vector pairings satisfies the same
bound when each operator acts with a uniform bound on the chosen vector. -/
theorem norm_mean_operator_pairing_le (x : Ω → H →L[ℂ] H)
    (v w : Ω → H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, ‖x i (v i)‖ ≤ δ * ‖v i‖) :
    ‖meanPairing x v w‖ ≤ δ * (finiteRMS v * finiteRMS w) := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    (𝔼 i, ‖inner ℂ (x i (v i)) (w i)‖) ≤
        𝔼 i, δ * (‖v i‖ * ‖w i‖) := by
      apply expect_le_expect
      intro i _
      exact (norm_inner_le_norm _ _).trans
        ((mul_le_mul_of_nonneg_right (hx i) (norm_nonneg _)).trans_eq (mul_assoc _ _ _))
    _ = δ * (𝔼 i, ‖v i‖ * ‖w i‖) := (mul_expect _ _ _).symm
    _ ≤ δ * (finiteRMS v * finiteRMS w) :=
      mul_le_mul_of_nonneg_left (expect_norm_mul_le_finiteRMS v w) hδ

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
-- module Solutions.OAIQ075_KS.KadisonKastler_ClippedPairingBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_mul_unitary _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_unitary_mul _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaged pairings controlled by bounded algebra elements -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Rescaling the two algebra arguments extends a unit-ball pairing bound
to any fixed operator-norm ball. -/
theorem pairing_le_of_unitBall (J : A →ₗ[ℂ] H) (V : H →L[ℂ] H) {K s : ℝ}
    (hK : ∀ a b : A, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖inner ℂ (V (J a)) (J b)‖ ≤ K)
    (hs : 0 < s) (a b : A) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) :
    ‖inner ℂ (V (J a)) (J b)‖ ≤ s ^ 2 * K := by
  let c : ℂ := (s⁻¹ : ℝ)
  have hc : ‖c‖ = s⁻¹ := by simp [c, hs.le]
  have hca : ‖c • a‖ ≤ 1 := by
    rw [norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hs.le)).trans_eq
      (inv_mul_cancel₀ hs.ne')
  have hcb : ‖c • b‖ ≤ 1 := by
    rw [norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)).trans_eq
      (inv_mul_cancel₀ hs.ne')
  have hh := hK (c • a) (c • b) hca hcb
  have he : ‖inner ℂ (V (J (c • a))) (J (c • b))‖ =
      s⁻¹ * s⁻¹ * ‖inner ℂ (V (J a)) (J b)‖ := by
    simp only [map_smul, inner_smul_left, inner_smul_right, norm_mul,
      starRingEnd_apply, norm_star, hc]
    ring
  rw [he] at hh
  calc
    _ = s ^ 2 * (s⁻¹ * s⁻¹ * ‖inner ℂ (V (J a)) (J b)‖) := by
      field_simp [hs.ne']
    _ ≤ s ^ 2 * K := mul_le_mul_of_nonneg_left hh (sq_nonneg s)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The two tracial clipping errors are controlled in root mean square,
while the retained pairing is tested entirely on bounded elements. -/
theorem averaged_pairing_le_of_fourth_moments (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a)
    (V : H →L[ℂ] H) (a b : ι → A) {K s : ℝ} (hs : 0 < s)
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (ha₂ : (𝔼 i, traceTwoNorm τ (a i) ^ 2) ≤ 1)
    (hb₂ : (𝔼 i, traceTwoNorm τ (b i) ^ 2) ≤ 1)
    (ha₄ : (𝔼 i, (τ.toLinearMap ((star (a i) * a i) ^ 2)).re) ≤ 12)
    (hb₄ : (𝔼 i, (τ.toLinearMap ((star (b i) * b i) ^ 2)).re) ≤ 12) :
    ‖𝔼 i, inner ℂ (V (J (a i))) (J (b i))‖ ≤
      s ^ 2 * K + (2 * Real.sqrt 12 / s) * ‖V‖ := by
  let v : ι → H := fun i => J (a i)
  let w : ι → H := fun i => J (b i)
  let vc : ι → H := fun i => J (spectralClip s (a i))
  let wc : ι → H := fun i => J (spectralClip s (b i))
  have hrms (x : ι → A) (hx : (𝔼 i, traceTwoNorm τ (x i) ^ 2) ≤ 1) :
      finiteRMS (fun i => J (x i)) ≤ 1 := by
    have hsq : finiteRMS (fun i => J (x i)) ^ 2 ≤ 1 := by
      simpa only [finiteRMS_sq, hJ] using hx
    nlinarith [finiteRMS_nonneg (fun i => J (x i))]
  have hv : finiteRMS v ≤ 1 := hrms a ha₂
  have hw : finiteRMS w ≤ 1 := hrms b hb₂
  have hvc : finiteRMS vc ≤ 1 :=
    (finiteRMS_mono vc v fun i => by
      simpa only [vc, v, hJ] using traceTwoNorm_spectralClip_le τ hs (a i)).trans hv
  have htail (x : ι → A)
      (hx : (𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re) ≤ 12) :
      finiteRMS (fun i => J (x i) - J (spectralClip s (x i))) ≤ Real.sqrt 12 / s := by
    have hsq : finiteRMS (fun i => J (x i) - J (spectralClip s (x i))) ^ 2 ≤
        12 / s ^ 2 := by
      simpa only [finiteRMS_sq, ← map_sub, hJ] using
        expect_traceTwoNorm_spectralClip_discard_sq_le τ x hs hx
    have he : (Real.sqrt 12 / s) ^ 2 = 12 / s ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    have hp : 0 ≤ Real.sqrt 12 / s := div_nonneg (Real.sqrt_nonneg _) hs.le
    nlinarith [he, finiteRMS_nonneg (fun i => J (x i) - J (spectralClip s (x i)))]
  have hda : finiteRMS (fun i => v i - vc i) ≤ Real.sqrt 12 / s := htail a ha₄
  have hdb : finiteRMS (fun i => w i - wc i) ≤ Real.sqrt 12 / s := htail b hb₄
  have hclip : ‖meanPairing (fun _ : ι => V) vc wc‖ ≤ s ^ 2 * K := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      (𝔼 i, ‖inner ℂ (V (vc i)) (wc i)‖) ≤ 𝔼 _ : ι, s ^ 2 * K :=
        expect_le_expect fun i _ => pairing_le_of_unitBall J V hK hs _ _
          (spectralClip_norm_le hs (a i)) (spectralClip_norm_le hs (b i))
      _ = _ := Fintype.expect_const _
  have herr₁ : ‖meanPairing (fun _ : ι => V) (fun i => v i - vc i) w‖ ≤
      ‖V‖ * (Real.sqrt 12 / s) := by
    apply (norm_mean_operator_pairing_le _ _ _ (norm_nonneg V)
      (fun i => V.le_opNorm _)).trans
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul hda hw (finiteRMS_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hs.le)).trans_eq
        (mul_one _)) (norm_nonneg V)
  have herr₂ : ‖meanPairing (fun _ : ι => V) vc (fun i => w i - wc i)‖ ≤
      ‖V‖ * (Real.sqrt 12 / s) := by
    apply (norm_mean_operator_pairing_le _ _ _ (norm_nonneg V)
      (fun i => V.le_opNorm _)).trans
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul hvc hdb (finiteRMS_nonneg _) zero_le_one).trans_eq
        (one_mul _)) (norm_nonneg V)
  have heq : meanPairing (fun _ : ι => V) v w =
      meanPairing (fun _ : ι => V) vc wc +
        meanPairing (fun _ : ι => V) (fun i => v i - vc i) w +
          meanPairing (fun _ : ι => V) vc (fun i => w i - wc i) := by
    unfold meanPairing
    rw [← expect_add_distrib, ← expect_add_distrib]
    apply expect_congr rfl
    intro i _
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  change ‖meanPairing (fun _ : ι => V) v w‖ ≤ _
  rw [heq]
  calc
    _ ≤ (‖meanPairing (fun _ : ι => V) vc wc‖ +
        ‖meanPairing (fun _ : ι => V) (fun i => v i - vc i) w‖) +
        ‖meanPairing (fun _ : ι => V) vc (fun i => w i - wc i)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (s ^ 2 * K + ‖V‖ * (Real.sqrt 12 / s)) + ‖V‖ * (Real.sqrt 12 / s) :=
      add_le_add (add_le_add hclip herr₁) herr₂
    _ = _ := by ring

/-- The cutoff `4 * sqrt 12` makes the two error terms half of the
operator norm, with retained-pairing coefficient `192`. -/
theorem averaged_pairing_le_one_ninety_two (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a)
    (V : H →L[ℂ] H) (a b : ι → A) {K : ℝ}
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (ha₂ : (𝔼 i, traceTwoNorm τ (a i) ^ 2) ≤ 1)
    (hb₂ : (𝔼 i, traceTwoNorm τ (b i) ^ 2) ≤ 1)
    (ha₄ : (𝔼 i, (τ.toLinearMap ((star (a i) * a i) ^ 2)).re) ≤ 12)
    (hb₄ : (𝔼 i, (τ.toLinearMap ((star (b i) * b i) ^ 2)).re) ≤ 12) :
    ‖𝔼 i, inner ℂ (V (J (a i))) (J (b i))‖ ≤ 192 * K + ‖V‖ / 2 := by
  have hs : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (4 * Real.sqrt 12) ^ 2 = 192 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  have hratio : 2 * Real.sqrt 12 / (4 * Real.sqrt 12) = (1 / 2 : ℝ) := by
    field_simp [hs.ne']
    ring
  have h := averaged_pairing_le_of_fourth_moments τ J hJ V a b
    (by positivity : 0 < 4 * Real.sqrt 12) hK ha₂ hb₂ ha₄ hb₄
  rw [hsq, hratio] at h
  nlinarith only [h]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DensePairingBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing pairing estimates from a dense set to operator norm -/

namespace KadisonKastler

variable {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A homogeneous pairing estimate on a dense image controls the operator
norm. This is used after the finite randomization and clipping argument. -/
theorem opNorm_le_of_dense_pairing (J : A → H) (hJ : DenseRange J)
    (V : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a b, ‖inner ℂ (V (J a)) (J b)‖ ≤ C * ‖J a‖ * ‖J b‖) :
    ‖V‖ ≤ C := by
  have hfull (x y : H) : ‖inner ℂ (V x) y‖ ≤ C * ‖x‖ * ‖y‖ :=
    hJ.induction_on₂ (isClosed_le (by fun_prop) (by fun_prop)) hbound x y
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  exact (Complex.re_le_norm _).trans (by simpa only [hx, hy, mul_one] using hfull x y)

variable [AddCommMonoid A] [Module ℂ A]

/-- It suffices to test the unit vectors in a dense linear image. -/
theorem opNorm_le_of_dense_unit_pairing (J : A →ₗ[ℂ] H) (hJ : DenseRange J)
    (V : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a b, ‖J a‖ ≤ 1 → ‖J b‖ ≤ 1 → ‖inner ℂ (V (J a)) (J b)‖ ≤ C) :
    ‖V‖ ≤ C := by
  apply opNorm_le_of_dense_pairing J hJ V hC
  intro a b
  by_cases ha : J a = 0
  · simp [ha]
  by_cases hb : J b = 0
  · simp [hb]
  have hna : 0 < ‖J a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖J b‖ := norm_pos_iff.mpr hb
  let ca : ℂ := (‖J a‖⁻¹ : ℝ)
  let cb : ℂ := (‖J b‖⁻¹ : ℝ)
  have hca : ‖ca‖ = ‖J a‖⁻¹ := by simp [ca]
  have hcb : ‖cb‖ = ‖J b‖⁻¹ := by simp [cb]
  have hja : ‖J (ca • a)‖ ≤ 1 := by
    rw [map_smul, norm_smul, hca, inv_mul_cancel₀ hna.ne']
  have hjb : ‖J (cb • b)‖ ≤ 1 := by
    rw [map_smul, norm_smul, hcb, inv_mul_cancel₀ hnb.ne']
  have hh := hbound (ca • a) (cb • b) hja hjb
  simp only [map_smul, inner_smul_left, inner_smul_right, norm_mul,
    starRingEnd_apply, norm_star, hca, hcb] at hh
  calc
    _ = (‖J a‖ * ‖J b‖) *
        (‖J b‖⁻¹ * (‖J a‖⁻¹ * ‖inner ℂ (V (J a)) (J b)‖)) := by
      field_simp [hna.ne', hnb.ne']
    _ ≤ (‖J a‖ * ‖J b‖) * C :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg hna.le hnb.le)
    _ = _ := by ring

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteSignFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_mul_unitary _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_unitary_mul _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth moments of finite independent signs

The finite probability space is the set of all Boolean sign assignments.
The four-sign identity and tracial Cauchy–Schwarz give the estimate used
in the bounded-vector test in manuscript §5.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem finiteSign_flip_same (ε : ι → Bool) (i : ι) :
    finiteSign (flipSign i ε) i = -finiteSign ε i := by
  cases h : ε i <;> simp [finiteSign, flipSign, h]

omit [Fintype ι] in
private theorem finiteSign_flip_ne (ε : ι → Bool) {i j : ι} (h : j ≠ i) :
    finiteSign (flipSign i ε) j = finiteSign ε j := by
  simp [finiteSign, flipSign, Function.update_of_ne h]

/-- Coordinate sign orthogonality. -/
theorem finiteSign_pair (i j : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true, if_true, ← pow_two, finiteSign_sq, Fintype.expect_const]
  · rw [ite_eq_right h]
    have he := Fintype.expect_equiv (flipSign i)
      (fun ε => finiteSign ε i * finiteSign ε j)
      (fun ε => -(finiteSign ε i * finiteSign ε j)) (by
        intro ε
        rw [finiteSign_flip_same, finiteSign_flip_ne ε (Ne.symm h)]
        ring)
    rw [Finset.expect_neg_distrib] at he
    linarith

/-- A sign appearing exactly once kills a four-sign expectation. -/
private theorem finiteSign_four_single (i j k l : ι)
    (hij : j ≠ i) (hik : k ≠ i) (hil : l ≠ i) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j *
      finiteSign ε k * finiteSign ε l) = 0 := by
  have he := Fintype.expect_equiv (flipSign i)
    (fun ε => finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l)
    (fun ε => -(finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l)) (by
      intro ε
      rw [finiteSign_flip_same, finiteSign_flip_ne ε hij,
        finiteSign_flip_ne ε hik, finiteSign_flip_ne ε hil]
      ring)
  rw [Finset.expect_neg_distrib] at he
  linarith

/-- The three pairings, with the common diagonal counted only once. -/
theorem finiteSign_four (i j k l : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j *
      finiteSign ε k * finiteSign ε l) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) -
      (if i = j ∧ j = k ∧ k = l then 2 else 0) := by
  by_cases hij : i = j
  · subst j
    have he (ε : ι → Bool) :
        finiteSign ε i * finiteSign ε i * finiteSign ε k * finiteSign ε l =
          finiteSign ε k * finiteSign ε l := by
      rw [← pow_two, finiteSign_sq, one_mul]
    simp_rw [he]
    rw [finiteSign_pair]
    by_cases hik : i = k <;> by_cases hkl : k = l <;>
      simp_all
    all_goals norm_num
  · by_cases hik : i = k
    · subst k
      have he (ε : ι → Bool) :
          finiteSign ε i * finiteSign ε j * finiteSign ε i * finiteSign ε l =
            finiteSign ε j * finiteSign ε l := by
        calc
          _ = finiteSign ε i ^ 2 * (finiteSign ε j * finiteSign ε l) := by ring
          _ = _ := by rw [finiteSign_sq, one_mul]
      simp_rw [he]
      rw [finiteSign_pair]
      simp [hij, Ne.symm hij]
    · by_cases hil : i = l
      · subst l
        have he (ε : ι → Bool) :
            finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε i =
              finiteSign ε j * finiteSign ε k := by
          calc
            _ = finiteSign ε i ^ 2 * (finiteSign ε j * finiteSign ε k) := by ring
            _ = _ := by rw [finiteSign_sq, one_mul]
        simp_rw [he]
        rw [finiteSign_pair]
        simp [hij, hik, Ne.symm hij]
      · rw [finiteSign_four_single i j k l (Ne.symm hij) (Ne.symm hik) (Ne.symm hil)]
        simp [hij, hik, hil]

/-- The fourth-sign identity integrated against any four-index coefficient. -/
theorem expect_finiteSign_four_sum (F : ι → ι → ι → ι → ℝ) :
    (𝔼 ε : ι → Bool, ∑ i, ∑ j, ∑ k, ∑ l,
      (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) * F i j k l) =
      (∑ i, ∑ k, F i i k k) + (∑ i, ∑ j, F i j i j) +
        (∑ i, ∑ j, F i j j i) - 2 * ∑ i, F i i i i := by
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_four,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [ite_and, Finset.mul_sum]

variable {B : Type*} [CStarAlgebra B]

omit [DecidableEq ι] in
private theorem fourth_integrand_expand (τ : FaithfulTracialState B)
    (a : ι → B) (ε : ι → Bool) :
    realTrace τ ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) *
          realTrace τ ((star (a i) * a j) * (star (a k) * a l)) := by
  have hprod : star (finiteSignSum a ε) * finiteSignSum a ε =
      ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) • (star (a i) * a j) := by
    simp only [finiteSignSum, star_sum, star_smul, star_trivial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_comm (finiteSign ε j) (finiteSign ε i)]
  rw [hprod, pow_two, Finset.sum_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [DecidableEq ι] in
private theorem realTrace_sum_square (τ : FaithfulTracialState B) (f : ι → B) :
    realTrace τ ((∑ i, f i) ^ 2) = ∑ i, ∑ j, realTrace τ (f i * f j) := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]

/-- Exact fourth-moment pairing formula before scalar normalization. -/
theorem expect_finiteSignSum_fourth (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool, realTrace τ ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) =
      realTrace τ ((∑ i, star (a i) * a i) ^ 2) +
        (∑ i, ∑ j, realTrace τ ((star (a i) * a j) ^ 2)) +
        realTrace τ ((∑ i, a i * star (a i)) ^ 2) -
        2 * ∑ i, realTrace τ ((star (a i) * a i) ^ 2) := by
  simp_rw [fourth_integrand_expand]
  rw [expect_finiteSign_four_sum]
  have hcross (i j : ι) :
      realTrace τ ((star (a i) * a j) * (star (a j) * a i)) =
        realTrace τ ((a i * star (a i)) * (a j * star (a j))) := by
    simp only [realTrace_apply]
    have ht : τ.toLinearMap ((star (a i) * a j) * (star (a j) * a i)) =
        τ.toLinearMap ((a i * star (a i)) * (a j * star (a j))) := by
      calc
        _ = τ.toLinearMap ((a j * (star (a j) * a i)) * star (a i)) := by
          rw [mul_assoc, τ.tracial (star (a i))]
        _ = τ.toLinearMap ((a j * star (a j)) * (a i * star (a i))) := by
          simp only [mul_assoc]
        _ = _ := τ.tracial _ _
    exact congrArg Complex.re ht
  have hsum : (∑ i, ∑ j, realTrace τ ((star (a i) * a j) * (star (a j) * a i))) =
      realTrace τ ((∑ i, a i * star (a i)) ^ 2) := by
    rw [realTrace_sum_square]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hcross i j
  rw [hsum, realTrace_sum_square τ (fun i => star (a i) * a i)]
  simp only [pow_two]

/-- Tracial Cauchy–Schwarz bounds the crossed pairing by a covariance term. -/
theorem realTrace_square_le_star_square (τ : FaithfulTracialState B) (x : B) :
    realTrace τ (x ^ 2) ≤ realTrace τ (star x * x) := by
  calc
    _ ≤ ‖τ.toLinearMap (x ^ 2)‖ := Complex.re_le_norm _
    _ ≤ traceTwoNorm τ x ^ 2 := by
      simpa only [star_star, traceTwoNorm_star, pow_two] using τ.cauchySchwarz (star x) x
    _ = _ := traceTwoNorm_sq τ x

/-- The unnormalized fourth moment is controlled by the two covariance squares. -/
theorem expect_finiteSignSum_fourth_le (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool, realTrace τ ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) ≤
      realTrace τ ((∑ i, star (a i) * a i) ^ 2) +
        2 * realTrace τ ((∑ i, a i * star (a i)) ^ 2) := by
  rw [expect_finiteSignSum_fourth]
  have hcross : (∑ i, ∑ j, realTrace τ ((star (a i) * a j) ^ 2)) ≤
      realTrace τ ((∑ i, a i * star (a i)) ^ 2) := by
    calc
      _ ≤ ∑ i, ∑ j, realTrace τ (star (star (a i) * a j) * (star (a i) * a j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          realTrace_square_le_star_square τ _
      _ = _ := by
        rw [realTrace_sum_square]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [realTrace_apply, star_mul, star_star]
        have ht := τ.tracial (star (a j)) (a i * (star (a i) * a j))
        simpa only [mul_assoc] using congrArg Complex.re ht
  have hdiag : 0 ≤ ∑ i, realTrace τ ((star (a i) * a i) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    simpa only [realTrace_apply, pow_two, star_mul, star_star] using
      τ.positive (star (a i) * a i)
  linarith

private theorem realTrace_square_smul (τ : FaithfulTracialState B) (t : ℝ) (x : B) :
    realTrace τ ((t • x) ^ 2) = t ^ 2 * realTrace τ (x ^ 2) := by
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, map_smul, smul_eq_mul]

private theorem realTrace_fourth_smul (τ : FaithfulTracialState B) (t : ℝ) (x : B) :
    realTrace τ ((star (t • x) * (t • x)) ^ 2) =
      t ^ 4 * realTrace τ ((star x * x) ^ 2) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, realTrace_square_smul]
  ring

/-- The normalized fourth moment is bounded by the two covariance squares. -/
theorem expect_normalizedFiniteSignSum_fourth_le
    (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool,
      realTrace τ ((star (normalizedFiniteSignSum a ε) * normalizedFiniteSignSum a ε) ^ 2)) ≤
      traceTwoNorm τ (finiteSignRightCovariance a) ^ 2 +
        2 * traceTwoNorm τ (finiteSignLeftCovariance a) ^ 2 := by
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 4 = (Fintype.card ι : ℝ)⁻¹ ^ 2 := by
    rw [inv_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _), inv_pow]
  have hright : star (finiteSignRightCovariance a) = finiteSignRightCovariance a := by
    simp [finiteSignRightCovariance, star_sum, star_smul, star_mul]
  have hleft : star (finiteSignLeftCovariance a) = finiteSignLeftCovariance a := by
    simp [finiteSignLeftCovariance, star_sum, star_smul, star_mul]
  have hright2 : traceTwoNorm τ (finiteSignRightCovariance a) ^ 2 =
      realTrace τ (finiteSignRightCovariance a ^ 2) := by
    simpa only [hright, pow_two, realTrace_apply] using
      traceTwoNorm_sq τ (finiteSignRightCovariance a)
  have hleft2 : traceTwoNorm τ (finiteSignLeftCovariance a) ^ 2 =
      realTrace τ (finiteSignLeftCovariance a ^ 2) := by
    simpa only [hleft, pow_two, realTrace_apply] using
      traceTwoNorm_sq τ (finiteSignLeftCovariance a)
  simp_rw [normalizedFiniteSignSum, realTrace_fourth_smul]
  rw [← Finset.mul_expect, hs, hright2, hleft2,
    finiteSignRightCovariance, finiteSignLeftCovariance,
    realTrace_square_smul, realTrace_square_smul]
  have h := mul_le_mul_of_nonneg_left (expect_finiteSignSum_fourth_le τ a)
    (sq_nonneg ((Fintype.card ι : ℝ)⁻¹))
  nlinarith only [h]

/-- Covariance two-norms bounded by two give the manuscript constant twelve. -/
theorem expect_normalizedFiniteSignSum_fourth_le_twelve
    (τ : FaithfulTracialState B) (a : ι → B)
    (hQ : traceTwoNorm τ (finiteSignRightCovariance a) ≤ 2)
    (hL : traceTwoNorm τ (finiteSignLeftCovariance a) ≤ 2) :
    (𝔼 ε : ι → Bool,
      (τ.toLinearMap ((star (normalizedFiniteSignSum a ε) *
        normalizedFiniteSignSum a ε) ^ 2)).re) ≤ 12 := by
  have h := expect_normalizedFiniteSignSum_fourth_le τ a
  have hQ0 := traceTwoNorm_nonneg τ (finiteSignRightCovariance a)
  have hL0 := traceTwoNorm_nonneg τ (finiteSignLeftCovariance a)
  change (𝔼 ε : ι → Bool,
    realTrace τ ((star (normalizedFiniteSignSum a ε) * normalizedFiniteSignSum a ε) ^ 2)) ≤ 12
  nlinarith

/-- Real signs also form an orthogonal family of complex phases. -/
theorem finiteSign_complex_pair (i j : ι) :
    (𝔼 ε : ι → Bool, star (finiteSign ε i : ℂ) * (finiteSign ε j : ℂ)) =
      if i = j then 1 else 0 := by
  let toC : ℝ →ₗ[ℚ≥0] ℂ := Complex.ofRealCLM.toLinearMap.restrictScalars ℚ≥0
  have h := congrArg toC (finiteSign_pair i j)
  rw [map_expect] at h
  simpa [toC, Complex.ofReal_mul] using h

private theorem expect_finiteSign_pair_sum (F : ι → ι → ℝ) :
    (𝔼 ε : ι → Bool, ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) * F i j) =
      ∑ i, F i i := by
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_pair]
  simp

/-- The second moment is the average of the coefficient two-norm squares. -/
theorem expect_normalizedFiniteSignSum_twoNorm_sq
    (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool, traceTwoNorm τ (normalizedFiniteSignSum a ε) ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, traceTwoNorm τ (a i) ^ 2 := by
  have hprod (ε : ι → Bool) :
      realTrace τ (star (finiteSignSum a ε) * finiteSignSum a ε) =
        ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) * realTrace τ (star (a i) * a j) := by
    simp only [finiteSignSum, star_sum, star_smul, star_trivial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, map_sum, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_comm (finiteSign ε j) (finiteSign ε i)]
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [traceTwoNorm_sq, normalizedFiniteSignSum, star_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  change (𝔼 ε : ι → Bool, realTrace τ
    (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * (Real.sqrt (Fintype.card ι : ℝ))⁻¹) •
      (star (finiteSignSum a ε) * finiteSignSum a ε))) = _
  simp_rw [map_smul, smul_eq_mul, ← pow_two, hs, hprod]
  rw [← Finset.mul_expect, expect_finiteSign_pair_sum]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq ι] in
private theorem map_normalizedFiniteSignSum_p0 (J : B →ₗ[ℂ] H) (a : ι → B) (ε : ι → Bool) :
    J (normalizedFiniteSignSum a ε) =
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) •
        finitePhaseSum (fun i ε => (finiteSign ε i : ℂ)) (fun i => J (a i)) ε := by
  simp only [normalizedFiniteSignSum, finiteSignSum, finitePhaseSum,
    ← Complex.coe_smul, map_smul, map_sum, Complex.ofReal_inv]

/-- Mixed sign orthogonality, with any complex-linear realization and bounded operator. -/
theorem expect_normalizedFiniteSignSum_pairing
    (J : B →ₗ[ℂ] H) (V : H →L[ℂ] H) (a b : ι → B) :
    (𝔼 ε : ι → Bool, inner ℂ (V (J (normalizedFiniteSignSum a ε)))
      (J (normalizedFiniteSignSum b ε))) =
      (Fintype.card ι : ℂ)⁻¹ * ∑ i, inner ℂ (V (J (a i))) (J (b i)) := by
  let χ (i : ι) (ε : ι → Bool) : ℂ := finiteSign ε i
  have hmap (ε : ι → Bool) :
      V (finitePhaseSum χ (fun i => J (a i)) ε) =
        finitePhaseSum χ (fun i => V (J (a i))) ε := by
    simp only [finitePhaseSum, map_sum, map_smul]
  have hc : star (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) = (Fintype.card ι : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← pow_two, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast]
  simp_rw [map_normalizedFiniteSignSum_p0, map_smul]
  change (𝔼 ε : ι → Bool, inner ℂ
    ((((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) •
      V (finitePhaseSum χ (fun i => J (a i)) ε))
    ((((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) •
      finitePhaseSum χ (fun i => J (b i)) ε)) = _
  simp_rw [hmap, inner_smul_left, inner_smul_right, starRingEnd_apply, ← mul_assoc, hc]
  rw [← Finset.mul_expect]
  congr 1
  exact finitePhaseSum_inner χ finiteSign_complex_pair _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCovariancePairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_mul_unitary _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_unitary_mul _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Testing balanced finite families by bounded algebra elements -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem normalized_sign_second_moment_le_one (τ : FaithfulTracialState A)
    (a : ι → A) (ha : ∀ i, traceTwoNorm τ (a i) ≤ 1) :
    (𝔼 ε : ι → Bool, traceTwoNorm τ (normalizedFiniteSignSum a ε) ^ 2) ≤ 1 := by
  rw [expect_normalizedFiniteSignSum_twoNorm_sq]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _ : ι, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun i _ => by
        nlinarith [traceTwoNorm_nonneg τ (a i), ha i]
    _ = 1 := by simp [Fintype.card_ne_zero]

/-- A balanced family has a bounded fourth moment after sign randomization.
Clipping then controls its common pairing by unit-ball tests. -/
theorem pairing_le_of_finite_covariances (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (V : H →L[ℂ] H) (a b : ι → A) {z : ℂ} {K : ℝ}
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (ha : ∀ i, traceTwoNorm τ (a i) ≤ 1)
    (hb : ∀ i, traceTwoNorm τ (b i) ≤ 1)
    (hQa : traceTwoNorm τ (finiteSignRightCovariance a) ≤ 2)
    (hLa : traceTwoNorm τ (finiteSignLeftCovariance a) ≤ 2)
    (hQb : traceTwoNorm τ (finiteSignRightCovariance b) ≤ 2)
    (hLb : traceTwoNorm τ (finiteSignLeftCovariance b) ≤ 2)
    (hz : ∀ i, inner ℂ (V (J (a i))) (J (b i)) = z) :
    ‖z‖ ≤ 192 * K + ‖V‖ / 2 := by
  have hmean : (𝔼 ε : ι → Bool,
      inner ℂ (V (J (normalizedFiniteSignSum a ε)))
        (J (normalizedFiniteSignSum b ε))) = z := by
    rw [expect_normalizedFiniteSignSum_pairing]
    simp [hz, Fintype.card_ne_zero]
  have h := averaged_pairing_le_one_ninety_two τ J hJ V
    (normalizedFiniteSignSum a) (normalizedFiniteSignSum b) hK
    (normalized_sign_second_moment_le_one τ a ha)
    (normalized_sign_second_moment_le_one τ b hb)
    (expect_normalizedFiniteSignSum_fourth_le_twelve τ a hQa hLa)
    (expect_normalizedFiniteSignSum_fourth_le_twelve τ b hQb hLb)
  rwa [hmean] at h

/-- Once finite families with the stated covariance bounds have been
constructed for each pair of tracial unit vectors, the bounded-ball test
constant is `384`. The family construction is kept as a separate task. -/
theorem opNorm_le_of_finite_covariance_families_oai (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hJdense : DenseRange J) (V : H →L[ℂ] H) {K : ℝ}
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (hfamilies : ∀ a b : A, traceTwoNorm τ a ≤ 1 → traceTwoNorm τ b ≤ 1 →
      ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → A,
        (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
        (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
        traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
        traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
        traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
        traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
        (∀ i, inner ℂ (V (J (f i))) (J (g i)) = inner ℂ (V (J a)) (J b))) :
    ‖V‖ ≤ 384 * K := by
  have hK0 : 0 ≤ K := by
    simpa using hK 0 0 (by simp) (by simp)
  have hV : ‖V‖ ≤ 192 * K + ‖V‖ / 2 := by
    apply opNorm_le_of_dense_unit_pairing J hJdense V (by positivity)
    intro a b ha hb
    rw [hJ] at ha hb
    obtain ⟨n, hn, f, g, hf, hg, hQf, hLf, hQg, hLg, hfg⟩ := hfamilies a b ha hb
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact pairing_le_of_finite_covariances τ J hJ V f g hK hf hg hQf hLf hQg hLg hfg
  linarith

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.opNorm_le_of_finite_covariance_families_oai.{u_1, u_2} := @OAI.KadisonKastler.opNorm_le_of_finite_covariance_families_oai.{u_1, u_2}
