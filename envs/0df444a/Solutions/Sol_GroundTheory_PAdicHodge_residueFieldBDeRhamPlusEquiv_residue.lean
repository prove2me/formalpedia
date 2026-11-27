-- Prove2me | solution 1 for GroundTheory.PAdicHodge.residueFieldBDeRhamPlusEquiv_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:46.280807+00:00
-- url     : https://prove2.me/submissions/4aaef7a7-d113-46d0-9e44-739007a12078

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus

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
open Ideal WittVector IsLocalRing
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R)))
    (x : BDeRhamPlus R p) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    residueFieldBDeRhamPlusEquiv hξ hF hK (residue (BDeRhamPlus R p) x) = thetaBDeRhamPlus R p x :=
  rfl
end GroundTheory.PAdicHodge
