-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.coe_untilt_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:43.552013+00:00
-- url     : https://prove2.me/submissions/5e6778c1-7a32-484f-a625-256d6425dc37

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    ((PreTilt.untilt (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) :
      normInteger ℂ_[p]) : ℂ_[p]) = σ • ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [untilt_preTiltMap, coe_integerMap]
  rfl
end GroundTheory.PAdicHodge.AInf
