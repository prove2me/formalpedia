-- Prove2me | solution 1 for GlobalTheory.TupleCone.one_mem_piece_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:50.803658+00:00
-- url     : https://prove2.me/submissions/048351bc-10c0-457f-9669-8ad031efdd11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_TupleCone_mem_piece

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
theorem _root_.solution : (1 : L) ∈ piece o t 0 := by
  simpa [mem_piece] using isIntegral_one
end GlobalTheory.TupleCone
