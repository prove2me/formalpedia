-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.mel_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:53.601587+00:00
-- url     : https://prove2.me/submissions/704eba3d-e0a6-40d7-861a-197825444509

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_conj_res
import Theorems.Thm_GlobalTheory_Hk_RayCont_conj_aChi

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
theorem _root_.solution (h : χ * χ = 1) (s : ℂ) :
    𝓕.mel χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.mel χ s) := by
  rw [LFam.mel, LFam.mel, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := zero_lt_one.trans ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_ne_zero.symm
  have h1 : (t : ℂ) ^ (-(starRingEnd ℂ) s - 1) = (starRingEnd ℂ) ((t : ℂ) ^ (-s - 1)) := by
    have := cpow_conj (t : ℂ) (-s - 1) harg
    rw [conj_ofReal, map_sub, map_neg, map_one] at this
    exact this
  simp only [map_mul, map_sub, map_sum, conj_aChi 𝓕 χ h, conj_res, conj_ofReal, h1]
end GlobalTheory.Hk.RayCont
