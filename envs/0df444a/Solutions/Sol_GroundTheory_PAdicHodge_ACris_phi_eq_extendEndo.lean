-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phi_eq_extendEndo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:16.568564+00:00
-- url     : https://prove2.me/submissions/c9598afe-7791-497d-9b2a-ebdc6331a551

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois

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
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution : phi K p = extendEndo (phiZero K p) :=
  rfl
end GroundTheory.PAdicHodge.ACris
