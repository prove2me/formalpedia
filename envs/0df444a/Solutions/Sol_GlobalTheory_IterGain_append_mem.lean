-- Prove2me | solution 1 for GlobalTheory.IterGain.append_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:37.183099+00:00
-- url     : https://prove2.me/submissions/75f52500-d7a3-4974-b030-8a720c68f3e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.IterGain
namespace GlobalTheory.IterGain
theorem _root_.solution {ι : Type} [DecidableEq ι] {B : Finset ι} {k : ℕ} {l : List ι} {i : ι}
    (hl : l ∈ words B k) (hi : i ∈ B) : l ++ [i] ∈ words B (k + 1) := by
  simp only [words, mem_insert, mem_image, mem_product, Prod.exists]
  exact Or.inr ⟨l, i, ⟨hl, hi⟩, rfl⟩
end GlobalTheory.IterGain
