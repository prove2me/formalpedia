-- Prove2me | solution 1 for GlobalTheory.RealZeros.summable_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:22.014157+00:00
-- url     : https://prove2.me/submissions/7a8983e8-8be8-4e24-9418-7682ed0eaaf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_norm_br_le
import Theorems.Thm_GlobalTheory_RealZeros_summable_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) {s : ℂ}
    (hs : 0 < s.re) : Summable fun k => br N c d k s :=
  Summable.of_norm_bounded (summable_bound (half_pos hs) ((‖s‖ + 1) * d))
    (fun k => norm_br_le hN hc hcd k (half_pos hs) (half_lt_self hs) (lt_add_one _))
end GlobalTheory.RealZeros
