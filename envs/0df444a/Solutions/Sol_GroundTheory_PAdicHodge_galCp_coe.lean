-- Prove2me | solution 1 for GroundTheory.PAdicHodge.galCp_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:15.5066+00:00
-- url     : https://prove2.me/submissions/7b04623a-2db2-4449-b87a-b9814bc2a3b1

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    galCp σ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
  gal_smul_coe σ y
end GroundTheory.PAdicHodge
