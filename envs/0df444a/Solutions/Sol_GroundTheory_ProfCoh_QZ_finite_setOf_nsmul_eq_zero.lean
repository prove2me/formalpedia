-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZ.finite_setOf_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:23.945854+00:00
-- url     : https://prove2.me/submissions/02869757-f91a-419d-a1b7-641392ca0576

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Function
open GroundTheory.ProfCoh.QZ
namespace GroundTheory.ProfCoh.QZ
theorem _root_.solution {n : ℕ} (hn : 0 < n) : {x : QZ | n • x = 0}.Finite :=
  AddCircle.finite_torsion (1 : ℚ) hn
end GroundTheory.ProfCoh.QZ
