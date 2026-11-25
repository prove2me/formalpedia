-- Prove2me | solution 1 for GlobalTheory.TupleCone.mul_mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:09:04.343977+00:00
-- url     : https://prove2.me/submissions/2af125f7-60cf-4409-bafd-6dd47a8c41ee

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
theorem _root_.solution {m n : ℕ} {a b : L} (ha : a ∈ piece o t m) (hb : b ∈ piece o t n) :
    a * b ∈ piece o t (m + n) := by
  have h := IsIntegral.mul ha hb
  rwa [mem_piece, map_mul, pow_add, mul_mul_mul_comm]
end GlobalTheory.TupleCone
