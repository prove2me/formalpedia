-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.gal_smul_frobeniusEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:15.426334+00:00
-- url     : https://prove2.me/submissions/4e2eeb99-743f-4597-a6bd-57a0b4465d29

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv

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
open GroundTheory.PAdicHodge.AInf
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • WittVector.frobeniusEquiv p _ x = WittVector.frobeniusEquiv p _ (σ • x) :=
  map_frobeniusEquiv _ _ x
end GroundTheory.PAdicHodge.AInf
