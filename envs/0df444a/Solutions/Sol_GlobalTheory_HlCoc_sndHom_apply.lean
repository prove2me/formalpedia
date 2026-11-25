-- Prove2me | solution 1 for GlobalTheory.HlCoc.sndHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:07:15.51089+00:00
-- url     : https://prove2.me/submissions/bdfb61b6-4bcc-44a8-9b64-b6cb6cde56cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
namespace GlobalTheory.HlCoc
theorem _root_.solution (p : SD M G) : sndHom p = p.2 := rfl
end GlobalTheory.HlCoc
