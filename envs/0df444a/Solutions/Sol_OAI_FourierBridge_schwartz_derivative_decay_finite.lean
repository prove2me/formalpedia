-- Prove2me | solution 1 for OAI.FourierBridge.schwartz_derivative_decay_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:44.824508+00:00
-- url     : https://prove2.me/submissions/9f52d800-375c-45a2-89d1-c5823a772228

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    (F : 𝓢(ℝ, ℂ)) (A K j i : ℕ) (u : ℝ)
    (hj : j ≤ K) (hi : i ≤ j) (hu : 0 ≤ u) :
    (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤
      schwartzDerivativeDecayConstant F (A + K) K := by
  let M := A + K
  let T : ℝ := (SchwartzMap.seminorm ℝ 0 i) F +
    (SchwartzMap.seminorm ℝ M i) F
  let N : ℝ := ‖iteratedFDeriv ℝ i F u‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (1 + u) ^ (A + j) ≤ (1 + u) ^ M :=
    pow_le_pow_right₀ (by linarith) (by dsimp [M]; omega)
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu M
  have htwo : (2 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
  have hsum : (1 + u) ^ M * N ≤ (2 : ℝ) ^ M *
      (N + u ^ M * N) := by
    calc
      (1 + u) ^ M * N ≤
          (2 : ℝ) ^ (M - 1) * (1 ^ M + u ^ M) * N :=
        mul_le_mul_of_nonneg_right hadd hN
      _ ≤ (2 : ℝ) ^ M * (1 ^ M + u ^ M) * N := by
        gcongr
      _ = (2 : ℝ) ^ M * (N + u ^ M * N) := by
        simp; ring
  have h0 : N ≤ (SchwartzMap.seminorm ℝ 0 i) F := by
    simpa [N] using SchwartzMap.le_seminorm ℝ 0 i F u
  have hM : u ^ M * N ≤ (SchwartzMap.seminorm ℝ M i) F := by
    simpa [N, Real.norm_eq_abs, abs_of_nonneg hu] using
      SchwartzMap.le_seminorm ℝ M i F u
  have hT : N + u ^ M * N ≤ T := add_le_add h0 hM
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hTsum : T ≤ ∑ k ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 k) F +
        (SchwartzMap.seminorm ℝ M k) F) := by
    apply Finset.single_le_sum
      (f := fun k : ℕ =>
        (SchwartzMap.seminorm ℝ 0 k) F +
          (SchwartzMap.seminorm ℝ M k) F)
      (a := i)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hi.trans hj))
  calc
    (1 + u) ^ (A + j) * N ≤ (1 + u) ^ M * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ ≤ (2 : ℝ) ^ M * (N + u ^ M * N) := hsum
    _ ≤ (2 : ℝ) ^ M * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2 : ℝ) ^ M *
        (∑ k ∈ Finset.range (K + 1),
          ((SchwartzMap.seminorm ℝ 0 k) F +
            (SchwartzMap.seminorm ℝ M k) F)) :=
      mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ = schwartzDerivativeDecayConstant F (A + K) K := rfl
end OAI.FourierBridge
