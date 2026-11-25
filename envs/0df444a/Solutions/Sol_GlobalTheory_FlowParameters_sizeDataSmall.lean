-- Prove2me | solution 1 for GlobalTheory.FlowParameters.sizeDataSmall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:58:29.300789+00:00
-- url     : https://prove2.me/submissions/79ddae01-57b6-4d00-9ed3-e98a06d5f5c7

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
import Theorems.Thm_GlobalTheory_FlowParameters_sum_inflow
import Theorems.Thm_GlobalTheory_FlowParameters_maxFlow_smul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowParameters
namespace GlobalTheory.FlowParameters
theorem _root_.solution : ParametersSmall := by
  intro l d _ hl hd n m θ S W ys y u mon cCH cMON cB eB hW _ hval _ hS hzero _ hmon hsplit
    hB hCH hMON
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hg : 0 ≤ gam l := div_nonneg (by positivity) (by nlinarith)
  have hn : (0 : ℝ) ≤ n := by positivity
  have hscale := maxFlow_smul_le l d n hn W hW

  have hWsum : ∑ a, W a = (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) + (∑ a, u a) + ∑ a, mon a := by
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_inflow d (fun a i => (y a i : ℝ))]

  have hBsum : ∑ a, ∑ i ∈ oddLevels d, cB a i ≤
      n * gam l * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (n * gam l - n) * (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) +
        ∑ a, ∑ i ∈ oddLevels d, eB a i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi => ?_
    have := hB a i hi
    linarith
  have hCHsum : ∑ a, cCH a ≤ n * gam l * (∑ a, u a) + m * (∑ a, u a) / ((l : ℝ) - 1) := by
    refine (Finset.sum_le_sum fun a _ => hCH a).trans (le_of_eq ?_)
    rw [← Finset.sum_mul]
    ring
  have hMONsum : ∑ a, cMON a ≤ (∑ a, mon a) / ((l : ℝ) - 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun a _ => hMON a

  have hround : flowVal d ys ≤ (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) +
      S * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
        (fun p => ys p.1 p.2 ≠ 0)).card := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.sum_product,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : ys a i = 0
    · simp [h]
    · have := hS a i
      simp only [ne_eq, h, not_false_eq_true, if_true, Nat.cast_one, mul_one]
      linarith
  have hmonsum : 0 ≤ n * gam l * ∑ a, mon a :=
    mul_nonneg (mul_nonneg hn hg) (Finset.sum_nonneg fun a _ => hmon a)
  have h1 := mul_le_mul_of_nonneg_left (hval.trans hround) hn
  have h2 : gam l * ∑ a, (n : ℝ) * W a = n * gam l * ∑ a, W a := by
    rw [← Finset.mul_sum]; ring
  have h3 := congrArg (fun t => n * gam l * t) hWsum
  unfold Fnum
  rw [h2]
  linarith
end GlobalTheory.FlowParameters
