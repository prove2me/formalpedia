-- Prove2me | solution 1 for GlobalTheory.NormIntegers.eq_bot_or_eq_span_of_fg_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:37.87542+00:00
-- url     : https://prove2.me/submissions/ad056387-5864-4ef5-b6ab-42006faf4ba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_NormIntegers_isPrincipal_of_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
open GlobalTheory.NormIntegers
variable {C : Type*} [NormedField C] [IsUltrametricDist C] {O : Type*} [CommRing O] [Algebra O C]
  (hO : (NormedField.valuation (K := C)).Integers O)
include hO
namespace GlobalTheory.NormIntegers
theorem _root_.solution {J : Ideal O} (hJ : J.FG) (hJ' : J ≠ ⊤) :
    J = ⊥ ∨ ∃ w : O, 0 < ‖algebraMap O C w‖ ∧ ‖algebraMap O C w‖ < 1 ∧ J = Ideal.span {w} := by
  obtain ⟨w, hw⟩ := isPrincipal_of_fg hO hJ
  rw [Ideal.submodule_span_eq] at hw
  by_cases h0 : w = 0
  · left; simp [hw, h0]
  · right
    refine ⟨w, (norm_pos_iff hO).2 h0, (norm_le_one hO w).lt_of_ne fun h => hJ' ?_, hw⟩
    rw [hw, Ideal.span_singleton_eq_top, isUnit_iff_norm_eq_one hO, h]
end GlobalTheory.NormIntegers
