-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_int_eq_of_isIntegral_of_mul_eq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:58.635401+00:00
-- url     : https://prove2.me/submissions/48a65a03-8f66-4331-819d-fdba67edc544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntRelationOfIsIntegralRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {x : ℂ} (hx : IsIntegral ℤ x) {n k : ℤ}
    (hn : n ≠ 0) (h : (n : ℂ) * x = k) : ∃ j : ℤ, (j : ℂ) = x := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hq : x = algebraMap ℚ ℂ ((k : ℚ) / n) := by
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_intCast]
    rw [eq_div_iff hn', mul_comm, h]
  rw [hq, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hx
  obtain ⟨j, hj⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  refine ⟨j, ?_⟩
  rw [hq, ← hj]
  simp
end GlobalTheory.CuspGL
