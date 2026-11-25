-- Prove2me | solution 1 for GlobalTheory.Glue.IsNTr.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:41.10138+00:00
-- url     : https://prove2.me/submissions/d614a62d-538f-406a-a478-2224e0bea2ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Theorems.Thm_GlobalTheory_Glue_IsNTr_apply_eq_of_mem_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open GlobalTheory GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
namespace GlobalTheory.Glue
namespace IsNTr
theorem _root_.solution {l n m : ℕ} [NeZero l] {F F' G G' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m G G') :
    IsNTr ε l n m (F + G) (F' + G') := by
  obtain ⟨h1, h2, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, hG, τ', hτ', e'⟩ := h'
  refine ⟨h1, h2, add_mem hF hG, τ, hτ, ?_⟩
  rw [mul_add, e, e', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_add, IsNTr.apply_eq_of_mem_adjoin hG ((hτ a).trans (hτ' a).symm)]
end IsNTr
end GlobalTheory.Glue
