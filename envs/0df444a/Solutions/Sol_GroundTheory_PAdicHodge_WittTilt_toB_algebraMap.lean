-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.toB_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:17.615589+00:00
-- url     : https://prove2.me/submissions/6cd830c4-421d-4ec3-889e-5d264317922b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift

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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (x : AInf K p) :
    toB K p (algebraMap (AInf K p) 𝔸 x) = algebraMap (WittVector p K♭) (teichLift K p).B (incl K p x) :=
  IsLocalization.lift_eq _ x
end GroundTheory.PAdicHodge.WittTilt
