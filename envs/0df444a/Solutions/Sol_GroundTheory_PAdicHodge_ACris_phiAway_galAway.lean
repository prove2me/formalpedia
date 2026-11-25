-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phiAway_galAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:16.457947+00:00
-- url     : https://prove2.me/submissions/b79e9ed3-fd40-4b1c-86e0-1944f5d0294e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_gal_smul_frobeniusEquiv
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (y : 𝔸) :
    phiAway ℂ_[p] p (galAway σ y) = galAway σ (phiAway ℂ_[p] p y) := by
  have h : (phiAway ℂ_[p] p).comp (galAway σ) = (galAway σ).comp (phiAway ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, galAway_algebraMap, phiAway_algebraMap,
        AInf.gal_smul_frobeniusEquiv])
  exact congrFun (congrArg DFunLike.coe h) y
end GroundTheory.PAdicHodge.ACris
