-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.norm_rem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:49.243228+00:00
-- url     : https://prove2.me/submissions/e6eff6b2-13b5-4b83-8405-d9e20403bc50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_res_eq

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
theorem _root_.solution (x : ℝ) (hx : 1 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by
  have h : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x =
      ∑ g, χ g * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.a g n - 𝓕.κ * x : ℝ) : ℂ) := by
    simp only [LFam.aChi, res_eq]
    rw [Finset.sum_comm, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    push_cast
    rw [← Finset.mul_sum]
    ring
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ => 10 * Real.sqrt x) fun g _ => ?_).trans ?_
  · rw [norm_mul, AddChar.norm_apply, one_mul, norm_real, Real.norm_eq_abs]
    exact 𝓕.count g x hx
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right 𝓕.card_le (by positivity : 0 ≤ 10 * Real.sqrt x)
    linarith
end GlobalTheory.Hk.RayCont
