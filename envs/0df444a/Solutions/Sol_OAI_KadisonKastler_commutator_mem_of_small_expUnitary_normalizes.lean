-- Prove2me | solution 1 for OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:09.138463+00:00
-- url     : https://prove2.me/submissions/caf3b42e-13b6-4b53-aae7-e1d5a46f4af2

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K007
import Definitions.Def_Q260K012

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExponentialRemainder
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.exponentialRemainder_zero _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform estimates for the exponential inverse near zero

These elementary Banach-algebra estimates are used to recover a small
normalizer's infinitesimal generator inside its invariant algebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [NormedRing A]

/-- A bound independent of the algebra and of commutation of the two elements. -/
theorem norm_pow_succ_sub_pow_succ_le (x y : A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1 : ℝ) * r ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y := by
      rw [pow_succ x (n + 1), pow_succ y (n + 1)]
      noncomm_ring
    calc
      _ ≤ ‖x ^ (n + 1)‖ * ‖x - y‖ + ‖x ^ (n + 1) - y ^ (n + 1)‖ * ‖y‖ := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ r ^ (n + 1) * ‖x - y‖ + ((n + 1 : ℝ) * r ^ n * ‖x - y‖) * r := by
        gcongr
        exact (norm_pow_le' x (Nat.succ_pos n)).trans (pow_le_pow_left₀ (norm_nonneg x) hx _)
      _ = (↑(n + 1) + 1 : ℝ) * r ^ (n + 1) * ‖x - y‖ := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- Differentiating a positive-degree exponential coefficient never gives
an absolute value larger than one. -/
theorem exponential_derivative_coefficient_le_one (n : ℕ) :
    ((n + 1 : ℝ) / (n + 1).factorial) ≤ 1 := by
  have hp : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  apply (div_le_one hp).mpr
  exact_mod_cast Nat.self_le_factorial (n + 1)

section ComplexAlgebra

variable [NormedAlgebra ℂ A] [CompleteSpace A]

theorem hasSum_exponentialRemainder (x : A) :
    HasSum (fun n : ℕ => ((n + 2).factorial⁻¹ : ℂ) • x ^ (n + 2))
      (exponentialRemainder x) := by
  have h := (hasSum_nat_add_iff' 2).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)
  simpa [exponentialRemainder, Finset.sum_range_succ, sub_add_eq_sub_sub] using h

omit [CompleteSpace A] in
theorem norm_exponential_term_sub_le (x y : A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖((n + 2).factorial⁻¹ : ℂ) • x ^ (n + 2) -
      ((n + 2).factorial⁻¹ : ℂ) • y ^ (n + 2)‖ ≤ r ^ (n + 1) * ‖x - y‖ := by
  have hc : ((n + 2 : ℝ) / (n + 2).factorial) ≤ 1 := by
    have h := exponential_derivative_coefficient_le_one (n + 1)
    norm_num [Nat.cast_add, add_assoc] at h ⊢
    exact h
  have hp : ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤
      (n + 2 : ℝ) * r ^ (n + 1) * ‖x - y‖ := by
    have h := norm_pow_succ_sub_pow_succ_le x y hr hx hy (n + 1)
    norm_num [Nat.cast_add, add_assoc] at h ⊢
    exact h
  calc
    _ = ((n + 2).factorial : ℝ)⁻¹ * ‖x ^ (n + 2) - y ^ (n + 2)‖ := by
      rw [← smul_sub, norm_smul]
      simp
    _ ≤ ((n + 2).factorial : ℝ)⁻¹ *
        ((n + 2 : ℝ) * r ^ (n + 1) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((n + 2 : ℝ) / (n + 2).factorial) * (r ^ (n + 1) * ‖x - y‖) := by ring
    _ ≤ 1 * (r ^ (n + 1) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := one_mul _

theorem norm_exponentialRemainder_sub_le (x y : A) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖exponentialRemainder x - exponentialRemainder y‖ ≤
      r / (1 - r) * ‖x - y‖ := by
  let f := fun n : ℕ => ((n + 2).factorial⁻¹ : ℂ) • x ^ (n + 2) -
    ((n + 2).factorial⁻¹ : ℂ) • y ^ (n + 2)
  let b := fun n : ℕ => r ^ (n + 1) * ‖x - y‖
  have hf : HasSum f (exponentialRemainder x - exponentialRemainder y) :=
    (hasSum_exponentialRemainder x).sub (hasSum_exponentialRemainder y)
  have hb : HasSum b (r / (1 - r) * ‖x - y‖) := by
    simpa [b, pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hasSum_geometric_of_lt_one hr hr1).mul_left r).mul_right ‖x - y‖
  have hbound (n : ℕ) : ‖f n‖ ≤ b n := norm_exponential_term_sub_le x y hr hx hy n
  rw [← hf.tsum_eq, ← hb.tsum_eq]
  exact (norm_tsum_le_tsum_norm (hb.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound)).trans
    (Summable.tsum_le_tsum hbound
      (hb.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound) hb.summable)

end ComplexAlgebra

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ClosedExponentialGenerator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering a small exponential generator in a closed subalgebra

The radius is absolute, independent of the ambient complex Banach algebra.
This is the logarithm-series step needed for a small exact normalizer.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped NNReal Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem norm_exponentialRemainder_le_third {x : A} (hx : ‖x‖ ≤ 1 / 4) :
    ‖exponentialRemainder x‖ ≤ (1 / 3 : ℝ) * ‖x‖ := by
  have h := norm_exponentialRemainder_sub_le x (0 : A)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hx (by simp)
  norm_num at h
  exact h

/-- A small element belongs to every closed complex subalgebra containing its
exponential. The contraction argument supplies a uniform inverse radius. -/
theorem mem_closedSubalgebra_of_exp_mem (S : Subalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (x : A) (hx : ‖x‖ ≤ 1 / 16)
    (hexp : NormedSpace.exp x ∈ S) : x ∈ S := by
  let s : Set A := Metric.closedBall 0 (1 / 4)
  have hs : IsClosed s := Metric.isClosed_closedBall
  let _ : CompleteSpace s := hs.completeSpace_coe
  have hzero : (0 : A) ∈ s := by simp [s]
  let _ : Nonempty s := ⟨⟨0, hzero⟩⟩
  have hx' : ‖x‖ ≤ 1 / 4 := by linarith
  have hexpNorm : ‖NormedSpace.exp x - 1‖ ≤ 1 / 12 := by
    have he : NormedSpace.exp x - 1 = exponentialRemainder x + x := by
      simp [exponentialRemainder]
    rw [he]
    have h := norm_exponentialRemainder_le_third hx'
    exact (norm_add_le _ _).trans (by linarith)
  let f : A → A := fun y => (NormedSpace.exp x - 1) - exponentialRemainder y
  have hfmem {y : A} (hy : y ∈ s) : f y ∈ s := by
    have hyn : ‖y‖ ≤ 1 / 4 := by simpa [s, dist_eq_norm] using hy
    have hr := norm_exponentialRemainder_le_third hyn
    have hn : ‖f y‖ ≤ 1 / 4 := (norm_sub_le _ _).trans (by linarith)
    simpa [s, dist_eq_norm] using hn
  let F : s → s := fun y => ⟨f y, hfmem y.property⟩
  have hF : ContractingWith (1 / 3 : ℝ≥0) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro y z
    have hyn : ‖(y : A)‖ ≤ 1 / 4 := by simpa [s, dist_eq_norm] using y.property
    have hzn : ‖(z : A)‖ ≤ 1 / 4 := by simpa [s, dist_eq_norm] using z.property
    have h := norm_exponentialRemainder_sub_le (y : A) (z : A)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hyn hzn
    change dist (f y) (f z) ≤ (↑(1 / 3 : ℝ≥0)) * dist (y : A) (z : A)
    rw [dist_eq_norm]
    have he : f y - f z = -(exponentialRemainder (y : A) - exponentialRemainder (z : A)) := by
      dsimp [f]
      abel
    rw [he, norm_neg]
    norm_num [dist_eq_norm] at h ⊢
    exact h
  have hxs : x ∈ s := by simpa [s, dist_eq_norm] using hx'
  let X : s := ⟨x, hxs⟩
  have hX : Function.IsFixedPt F X := by
    apply Subtype.ext
    change (NormedSpace.exp x - 1) - exponentialRemainder x = x
    simp [exponentialRemainder]
  have hlim : Tendsto (fun n : ℕ => ((F^[n] ⟨0, hzero⟩ : s) : A)) atTop (𝓝 x) := by
    have h := (continuous_subtype_val.tendsto (ContractingWith.fixedPoint F hF)).comp
      (hF.tendsto_iterate_fixedPoint ⟨0, hzero⟩)
    rw [← hF.fixedPoint_unique hX] at h
    exact h
  have hremain : ∀ n : ℕ, ((F^[n] ⟨0, hzero⟩ : s) : A) ∈ S := by
    intro n
    induction n with
    | zero => exact S.zero_mem
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change f ((F^[n] ⟨0, hzero⟩ : s) : A) ∈ S
      apply S.sub_mem (S.sub_mem hexp S.one_mem)
      apply S.sub_mem (S.sub_mem ?_ S.one_mem) ih
      let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
      exact NormedSpace.exp_mem (R := ℂ) (s := S) hS ih
  exact hS.mem_of_tendsto hlim (Filter.Eventually.of_forall hremain)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExponentialCommutator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exponentiating a bounded inner derivation -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem norm_boundedCommutator_le (x : A) : ‖boundedCommutator x‖ ≤ 2 * ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖x * y - y * x‖ ≤ _
  calc
    _ ≤ ‖x * y‖ + ‖y * x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

omit [CompleteSpace A] in
private theorem leftMul_pow_apply (x y : A) (n : ℕ) :
    ((ContinuousLinearMap.mul ℂ A x) ^ n) y = x ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change x * (((ContinuousLinearMap.mul ℂ A x) ^ n) y) = _
    rw [ih, pow_succ', mul_assoc]

omit [CompleteSpace A] in
private theorem rightMul_pow_apply (x y : A) (n : ℕ) :
    (((ContinuousLinearMap.mul ℂ A).flip x) ^ n) y = y * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((((ContinuousLinearMap.mul ℂ A).flip x) ^ n) y) * x = _
    rw [ih, pow_succ, mul_assoc]

private theorem exp_leftMul_apply (x y : A) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ A x) y = NormedSpace.exp x * y := by
  have h := (ContinuousLinearMap.apply ℂ A y).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (ContinuousLinearMap.mul ℂ A x))
  change HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) •
    ((ContinuousLinearMap.mul ℂ A x) ^ n) y)
    (NormedSpace.exp (ContinuousLinearMap.mul ℂ A x) y) at h
  simp only [leftMul_pow_apply] at h
  have h' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) • (x ^ n * y))
      (NormedSpace.exp x * y) := by
    simpa only [smul_mul_assoc] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).mul_right y
  exact h.unique h'

private theorem exp_rightMul_apply (x y : A) :
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ A).flip x) y = y * NormedSpace.exp x := by
  have h := (ContinuousLinearMap.apply ℂ A y).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((ContinuousLinearMap.mul ℂ A).flip x))
  change HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) •
    (((ContinuousLinearMap.mul ℂ A).flip x) ^ n) y)
    (NormedSpace.exp ((ContinuousLinearMap.mul ℂ A).flip x) y) at h
  simp only [rightMul_pow_apply] at h
  have h' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) • (y * x ^ n))
      (y * NormedSpace.exp x) := by
    simpa only [mul_smul_comm] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).mul_left y
  exact h.unique h'

/-- The identity holds in every complete complex normed algebra. -/
theorem exp_boundedCommutator_apply (x y : A) :
    NormedSpace.exp (boundedCommutator x) y =
      NormedSpace.exp x * y * NormedSpace.exp (-x) := by
  let : NormedAlgebra ℚ (A →L[ℂ] A) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hc : Commute (ContinuousLinearMap.mul ℂ A x)
      (-((ContinuousLinearMap.mul ℂ A).flip x)) := by
    apply Commute.neg_right
    apply ContinuousLinearMap.ext
    intro z
    change x * (z * x) = (x * z) * x
    exact (mul_assoc _ _ _).symm
  rw [boundedCommutator, sub_eq_add_neg, NormedSpace.exp_add_of_commute hc]
  have he : -((ContinuousLinearMap.mul ℂ A).flip x) =
      (ContinuousLinearMap.mul ℂ A).flip (-x) := by rw [map_neg]
  rw [he]
  change NormedSpace.exp (ContinuousLinearMap.mul ℂ A x)
    (NormedSpace.exp ((ContinuousLinearMap.mul ℂ A).flip (-x)) y) = _
  rw [exp_leftMul_apply, exp_rightMul_apply, mul_assoc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerLogarithm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The logarithm of a small normalizer preserves the algebra

The bounded operators preserving a closed linear subspace form a closed
subalgebra. Uniform exponential inversion recovers the commutator generator
inside that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem preservingOperatorAlgebra_isClosed (P : VonNeumannAlgebra H) :
    IsClosed (preservingOperatorAlgebra P :
      Set ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))) := by
  have he : (preservingOperatorAlgebra P : Set ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))) =
      ⋂ a : Algebra P, {T | T (a : H →L[ℂ] H) ∈ P} := by
    ext T
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h a => h a a.property, fun h a ha => h ⟨a, ha⟩⟩
  rw [he]
  exact isClosed_iInter fun a => (isClosed_algebra P).preimage
    ((ContinuousLinearMap.apply ℂ (H →L[ℂ] H) a.val).continuous)

/-- In the absolute logarithm radius, conjugation invariance implies
invariance under the bounded commutator. -/
theorem commutator_mem_of_small_expUnitary_normalizes_oai
    (P : VonNeumannAlgebra H) (h : selfAdjoint (H →L[ℂ] H))
    (hsmall : ‖(h : H →L[ℂ] H)‖ ≤ 1 / 32)
    (hnormalizes : Conjugates (H := H) (selfAdjoint.expUnitary h) P P) :
    ∀ a ∈ P, (h : H →L[ℂ] H) * a - a * (h : H →L[ℂ] H) ∈ P := by
  let D := boundedCommutator (Complex.I • (h : H →L[ℂ] H))
  have hDnorm : ‖D‖ ≤ 1 / 16 := by
    have hn := norm_boundedCommutator_le (Complex.I • (h : H →L[ℂ] H))
    simp only [norm_smul, Complex.norm_I, one_mul] at hn
    exact hn.trans (by linarith)
  have hexp : NormedSpace.exp D ∈ preservingOperatorAlgebra P := by
    intro a ha
    rw [exp_boundedCommutator_apply]
    have hn := hnormalizes
    change unitaryConj (H := H) (selfAdjoint.expUnitary h) '' (P : Set (H →L[ℂ] H)) =
      (P : Set (H →L[ℂ] H)) at hn
    have hm : unitaryConj (H := H) (selfAdjoint.expUnitary h) a ∈ P := by
      change unitaryConj (H := H) (selfAdjoint.expUnitary h) a ∈ (P : Set (H →L[ℂ] H))
      rw [← hn]
      exact ⟨a, ha, rfl⟩
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    simp only [unitaryConj, selfAdjoint.expUnitary_coe, NormedSpace.star_exp,
      star_smul, Complex.star_def, Complex.conj_I, h.property.star_eq, neg_smul]
  have hD := mem_closedSubalgebra_of_exp_mem (preservingOperatorAlgebra P)
    (preservingOperatorAlgebra_isClosed P) D hDnorm hexp
  intro a ha
  have hi := P.smul_mem (hD a ha) (-Complex.I)
  change (-Complex.I) • ((Complex.I • (h : H →L[ℂ] H)) * a -
    a * (Complex.I • (h : H →L[ℂ] H))) ∈ P at hi
  simpa only [smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    neg_mul, Complex.I_mul_I, neg_neg, one_smul] using hi

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes_oai.{u_1} := @OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes_oai.{u_1}
