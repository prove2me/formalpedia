-- Prove2me | solution 1 for GlobalTheory.TupleCone.span_pow_le_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:26:46.08198+00:00
-- url     : https://prove2.me/submissions/2cb333d1-a5cf-4e52-83d4-fce3f297e7c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_TupleCone_piece_mul_le
import Theorems.Thm_GlobalTheory_TupleCone_mem_piece_one
import Theorems.Thm_GlobalTheory_TupleCone_one_mem_piece_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution (n : ℕ) : Submodule.span o (Set.range t) ^ n ≤ piece o t n := by
  induction n with
  | zero => rw [pow_zero, Submodule.one_le]; exact one_mem_piece_zero
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih (Submodule.span_le.mpr ?_)).trans (piece_mul_le n 1)
    rintro _ ⟨s, rfl⟩
    exact mem_piece_one s
end GlobalTheory.TupleCone
