-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.thetaZero_gal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:47.934049+00:00
-- url     : https://prove2.me/submissions/ce321d1e-6d60-4466-be8b-b5687dbcd627

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_gal_smul_zero
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_thetaAway_galAway
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_thetaZero


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
    ((thetaZero ℂ_[p] p (σ • y) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((thetaZero ℂ_[p] p y : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [coe_thetaZero, coe_thetaZero, coe_gal_smul_zero, thetaAway_galAway]
end GroundTheory.PAdicHodge.ACris
