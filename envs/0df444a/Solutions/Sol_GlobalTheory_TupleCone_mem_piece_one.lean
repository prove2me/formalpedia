-- Prove2me | solution 1 for GlobalTheory.TupleCone.mem_piece_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:09.611856+00:00
-- url     : https://prove2.me/submissions/c8eb55d6-9309-453b-9b0b-f32fe54eede2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_TupleCone_mem_piece
import Theorems.Thm_GlobalTheory_TupleCone_C_mul_X_mem_cone

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
theorem _root_.solution (s : σ) : t s ∈ piece o t 1 := by
  rw [mem_piece, pow_one]
  exact isIntegral_algebraMap (x := (⟨_, C_mul_X_mem_cone s⟩ : cone o t))
end GlobalTheory.TupleCone
