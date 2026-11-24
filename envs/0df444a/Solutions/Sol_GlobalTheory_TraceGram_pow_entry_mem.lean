-- Prove2me | solution 1 for GlobalTheory.TraceGram.pow_entry_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:12.242599+00:00
-- url     : https://prove2.me/submissions/0572626e-3f25-4c0f-867f-e0ef8e068439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntryMemSubringOfTraceGramUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.TraceGram
namespace GlobalTheory.TraceGram
theorem _root_.solution {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ O) (k : ℕ) : ∀ i j, (g ^ k) i j ∈ O := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (ih i l) (hg l j)
end GlobalTheory.TraceGram
