-- Prove2me | solution 1 for GlobalTheory.CuspGL.conv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:04:02.20184+00:00
-- url     : https://prove2.me/submissions/cb406626-5103-4be1-a693-0762ee8b0bce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
import Theorems.Thm_GlobalTheory_CuspGL_conv_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (a b : F[X] → ℂ) (P : F[X]) : conv a b P = conv b a P := by
  rw [conv_eq_sum, conv_eq_sum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; exact mul_comm _ _
end GlobalTheory.CuspGL
