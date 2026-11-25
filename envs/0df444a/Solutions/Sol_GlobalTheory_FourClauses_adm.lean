-- Prove2me | solution 1 for GlobalTheory.FourClauses.adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:33.969933+00:00
-- url     : https://prove2.me/submissions/d80d80e4-a5d2-42d2-bba1-4fcefdb745c7

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsSideMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace GlobalTheory.FourClauses
theorem _root_.solution : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun h k _ _ _ _ n V _ _ π hs hi => (h k).1 (Fin n) V π hs hi
end GlobalTheory.FourClauses
