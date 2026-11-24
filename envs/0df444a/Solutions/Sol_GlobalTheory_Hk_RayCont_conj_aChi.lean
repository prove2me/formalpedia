-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.conj_aChi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:24.958934+00:00
-- url     : https://prove2.me/submissions/febab581-bdb4-40ed-ac03-019aa066138c

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
theorem _root_.solution (h : χ * χ = 1) (n : ℕ) : (starRingEnd ℂ) (𝓕.aChi χ n) = 𝓕.aChi χ n := by
  rw [LFam.aChi, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : χ g * χ g = 1 := by
    have := DFunLike.congr_fun h g
    simpa using this
  rw [map_mul, conj_ofReal]
  rcases mul_self_eq_one_iff.1 h1 with h2 | h2 <;> simp [h2]
end GlobalTheory.Hk.RayCont
