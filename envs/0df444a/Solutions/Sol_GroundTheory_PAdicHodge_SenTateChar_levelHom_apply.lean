-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.levelHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:33.139827+00:00
-- url     : https://prove2.me/submissions/2b01ff90-4039-4a7c-b23a-35f42ac2a2f5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (u : unitsOneAdd p k) :
    levelHom p k hk u = Multiplicative.ofAdd (PadicInt.toZMod (levelQuot u)) := rfl
end GroundTheory.PAdicHodge.SenTateChar
