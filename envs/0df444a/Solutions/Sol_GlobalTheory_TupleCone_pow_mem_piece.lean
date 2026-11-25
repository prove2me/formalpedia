-- Prove2me | solution 1 for GlobalTheory.TupleCone.pow_mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:12.743382+00:00
-- url     : https://prove2.me/submissions/fffddf4a-58ca-4e80-b898-5673ff6777a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_TupleCone_span_pow_le_piece

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
theorem _root_.solution (s : σ) (n : ℕ) : t s ^ n ∈ piece o t n :=
  span_pow_le_piece n (Submodule.pow_mem_pow _ (Submodule.subset_span (Set.mem_range_self s)) n)
end GlobalTheory.TupleCone
