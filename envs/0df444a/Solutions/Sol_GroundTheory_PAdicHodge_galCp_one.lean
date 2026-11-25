-- Prove2me | solution 1 for GroundTheory.PAdicHodge.galCp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:17.257107+00:00
-- url     : https://prove2.me/submissions/52859a97-f9c0-4933-b306-33b48ee25aa0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter
noncomputable section
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution : galCp (1 : Gal(PadicAlgCl p/K)) = RingEquiv.refl ℂ_[p] :=
  map_one galCpHom
end GroundTheory.PAdicHodge
