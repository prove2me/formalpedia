-- Prove2me | solution 1 for GlobalTheory.TupleCone.mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:21.356627+00:00
-- url     : https://prove2.me/submissions/7e790852-df54-4d94-a532-1fb5f30c100a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin

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
theorem _root_.solution {n : ℕ} {a : L} : a ∈ piece o t n ↔ IsIntegral (cone o t) (C a * X ^ n) := Iff.rfl
end GlobalTheory.TupleCone
