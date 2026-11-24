-- Prove2me | solution 1 for GlobalTheory.RegBound.piece_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:10.559814+00:00
-- url     : https://prove2.me/submissions/6d3b7723-ea93-4da7-9743-f603560298a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (e : ℕ) :
    piece I e ≤ piece J e := fun _ hF => ⟨hF.1, h hF.2⟩
end GlobalTheory.RegBound
