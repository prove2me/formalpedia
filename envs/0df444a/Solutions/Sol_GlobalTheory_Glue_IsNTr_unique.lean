-- Prove2me | solution 1 for GlobalTheory.Glue.IsNTr.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:51.379186+00:00
-- url     : https://prove2.me/submissions/415c723a-b380-4b16-8f5a-c9945731c6ce

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
theorem _root_.solution {l n m : ℕ} [NeZero l] {F F' F'' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m F F'') : F' = F'' := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨-, -, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, -, τ', hτ', e'⟩ := h'
  refine mul_left_cancel₀ (pow_ne_zero (n - m) (Nat.cast_ne_zero.2 (NeZero.ne l))) (e.trans (Eq.trans ?_ e'.symm))
  exact Finset.sum_congr rfl fun a _ => IsNTr.apply_eq_of_mem_adjoin hF ((hτ a).trans (hτ' a).symm)
end IsNTr
end GlobalTheory.Glue
