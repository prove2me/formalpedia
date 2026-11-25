-- Prove2me | solution 1 for GroundTheory.PAdicHodge.galCp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:16.376364+00:00
-- url     : https://prove2.me/submissions/eb74951d-647c-4b90-8ac8-a525eb0ddae5

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
theorem _root_.solution (σ τ : Gal(PadicAlgCl p/K)) : galCp (σ * τ) = (galCp τ).trans (galCp σ) :=
  map_mul galCpHom σ τ
end GroundTheory.PAdicHodge
