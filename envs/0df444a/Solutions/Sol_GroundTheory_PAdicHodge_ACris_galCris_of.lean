-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.galCris_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:47.876992+00:00
-- url     : https://prove2.me/submissions/7fe9c4d7-100f-474d-b1b8-64ec0a8c93e2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois

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
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    galCris σ (AdicCompletion.of _ _ y) = AdicCompletion.of _ _ (σ • y) :=
  extendEndo_of _ y
end GroundTheory.PAdicHodge.ACris
