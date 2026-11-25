-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.gal_smul_algebraMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:34.84368+00:00
-- url     : https://prove2.me/submissions/d5dd40a3-b6a2-4fe5-9816-f90d7d8bbed9

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) x =
      algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) (σ • x) :=
  Subtype.ext (galAway_algebraMap σ x)
end GroundTheory.PAdicHodge.ACris
