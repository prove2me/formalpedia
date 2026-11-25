-- Prove2me | solution 1 for GroundTheory.PAdicHodge.continuous_galCp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:26.001805+00:00
-- url     : https://prove2.me/submissions/8693c886-cd21-4d0c-9e1c-04925eb37b4d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Theorems.Thm_GroundTheory_PAdicHodge_isometry_galCp

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) : Continuous (galCp σ) :=
  (isometry_galCp σ).continuous
end GroundTheory.PAdicHodge
