-- Prove2me | solution 1 for GlobalTheory.TraceGram.adjugate_entry_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:10.299621+00:00
-- url     : https://prove2.me/submissions/ac3d2e46-6e6d-4bee-84b6-eae1407ddbc4

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
    (G : Matrix (Fin n) (Fin n) K) (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let G' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨G i j, hG i j⟩
  have h : O.subtype.mapMatrix G' = G := by
    ext i j; rfl
  rw [← h, ← RingHom.map_adjugate]
  exact (G'.adjugate i j).2
end GlobalTheory.TraceGram
