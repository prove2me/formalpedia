-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.gal_smul_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:42.9868+00:00
-- url     : https://prove2.me/submissions/c4cd2f22-9e44-4ee5-8faf-9dd0cdf9dc71

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) (n : ℕ) :
    (σ • x).coeff n = preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) (x.coeff n) :=
  map_coeff _ _ x n
end GroundTheory.PAdicHodge.AInf
