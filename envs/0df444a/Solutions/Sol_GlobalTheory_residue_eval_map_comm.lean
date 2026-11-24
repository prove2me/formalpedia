-- Prove2me | solution 1 for GlobalTheory.residue_eval_map_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:31.998797+00:00
-- url     : https://prove2.me/submissions/0bd03dec-7ec8-462c-b7a4-4a69a88512c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (q : A[X]) (f : A →+* B) (h : B →+* C) (x : B) :
    h ((q.map f).eval x) = (q.map (h.comp f)).eval (h x) := by
  rw [eval_map, eval_map, hom_eval₂]
end GlobalTheory
