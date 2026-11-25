-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:01:56.797648+00:00
-- url     : https://prove2.me/submissions/83f3c045-4e15-4abd-bd81-97050ed92a9f

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
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    maximalIdeal (BDeRhamPlus R p) = span {wittToBDeRhamPlus R p ξ} :=
  (maximalIdeal_bDeRhamPlus hξ hF hK).trans (ker_thetaBDeRhamPlus hξ)
end GroundTheory.PAdicHodge
