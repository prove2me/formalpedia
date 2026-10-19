-- Prove2me | solution 1 for MazurTransfer.Order13InfinityLocalParameter.maximalIdeal_eq_span_z
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:39:11.588969+00:00
-- url     : https://prove2.me/submissions/2ab5393d-006a-4482-b5d0-fb9b3e3e0c16

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the reciprocal coordinate z generates the maximal ideal
of the actual chart localized at either infinity evaluation, in characteristic
different from two. Named downstream consumer: the order of the Pell function
at infinity. No valuation order or principal-divisor formula is assumed.
-/
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingCoordinates
import Theorems.Thm_MazurTransfer_Order13InfinityEvaluationKernel_evaluation_kernel
import Theorems.Thm_MazurTransfer_Order13InfinityLocalParameter_w_add_constant_isUnit
noncomputable section
universe u
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections Order13InfinityEvaluationKernel Order13InfinityLocalParameter
variable (K : Type u) [Field K] (a : K) (ha : a ^ 2 = 1)
namespace MazurTransfer.InfinityUniformizerHelpers20261017
theorem reciprocalInfinityEvaluation_z (a : K) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation K a ha (zCoordinate K) = 0 := by
  simp [reciprocalInfinityEvaluation, InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation, zCoordinate, AdjoinRoot.lift_of]
theorem difference_product :
    (w K a ha - constant K a ha) * (w K a ha + constant K a ha) =
      z K a ha * (z K a ha ^ 5 + 4 * z K a ha ^ 4 + 6 * z K a ha ^ 3 +
        2 * z K a ha ^ 2 + z K a ha + 2) := by
  have hw := congrArg (algebraMap (ReciprocalRing K) (LocalRing K a ha)) (wCoordinate_sq K)
  simp only [reciprocalPolynomial, map_add, map_mul, map_pow,
    _root_.map_ofNat, _root_.map_one, aeval_X] at hw
  have hc : constant K a ha ^ 2 = 1 := by
    dsimp [constant]
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  change w K a ha ^ 2 = _ at hw
  change _ = z K a ha ^ 6 + 4 * z K a ha ^ 5 + 6 * z K a ha ^ 4 +
    2 * z K a ha ^ 3 + z K a ha ^ 2 + 2 * z K a ha + 1 at hw
  linear_combination hw - hc

theorem difference_mem_span_z (h2 : (2 : K) ≠ 0) :
    w K a ha - constant K a ha ∈ Ideal.span {z K a ha} := by
  apply (Ideal.mul_unit_mem_iff_mem _ (w_add_constant_isUnit K a ha h2)).mp
  rw [difference_product]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

end MazurTransfer.InfinityUniformizerHelpers20261017
open MazurTransfer.InfinityUniformizerHelpers20261017
theorem solution (h2 : (2 : K) ≠ 0) :
    IsLocalRing.maximalIdeal (LocalRing K a ha) = Ideal.span {z K a ha} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    change RingHom.ker (evaluation K a ha) ≤ _
    rw [evaluation_kernel]
    apply Ideal.span_le.mpr
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact Ideal.subset_span (by simp [z])
    · change algebraMap (ReciprocalRing K) (LocalRing K a ha)
        (wCoordinate K - algebraMap K (ReciprocalRing K) a) ∈ Ideal.span {z K a ha}
      rw [map_sub]
      exact difference_mem_span_z K a ha h2
  · apply Ideal.span_le.mpr
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    apply Ideal.mem_map_of_mem
    exact MazurTransfer.InfinityUniformizerHelpers20261017.reciprocalInfinityEvaluation_z K a ha

#print axioms solution
