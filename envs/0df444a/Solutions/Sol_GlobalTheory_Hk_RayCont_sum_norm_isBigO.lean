-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.sum_norm_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:49.843139+00:00
-- url     : https://prove2.me/submissions/b950cd20-9739-44bd-9aec-7b8329ca68fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖𝓕.aChi χ k‖) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Fintype.card 𝓕.G * 14) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.rpow_one, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ∀ k, ‖𝓕.aChi χ k‖ ≤ ∑ g, 𝓕.a g k := fun k => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => le_of_eq ?_)
    rw [norm_mul, AddChar.norm_apply, one_mul, norm_real, Real.norm_of_nonneg (𝓕.a_nonneg g k)]
  refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum (g := fun _ => 14 * (n : ℝ)) fun g _ => ?_).trans (le_of_eq ?_)
  · have h := (abs_le.1 (𝓕.count g n hn1)).2
    rw [Nat.floor_natCast] at h
    have h2 : Real.sqrt n ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    have h3 : 𝓕.κ * n ≤ 4 * n := mul_le_mul_of_nonneg_right 𝓕.κ_le (by positivity)
    linarith
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
end GlobalTheory.Hk.RayCont
