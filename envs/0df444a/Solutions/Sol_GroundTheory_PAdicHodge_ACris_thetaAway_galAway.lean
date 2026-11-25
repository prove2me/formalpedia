-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.thetaAway_galAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:52.374515+00:00
-- url     : https://prove2.me/submissions/df2e10e0-c974-444d-8182-344d4361e206

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_gal_smul
import Theorems.Thm_GroundTheory_PAdicHodge_galCp_apply
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
    thetaAway ℂ_[p] p (galAway σ y) = σ • thetaAway ℂ_[p] p y := by
  have h : (thetaAway ℂ_[p] p).comp (galAway σ) =
      ((galCp σ : ℂ_[p] ≃+* ℂ_[p]) : ℂ_[p] →+* ℂ_[p]).comp (thetaAway ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, galAway_algebraMap, thetaAway_algebraMap, RingEquiv.coe_toRingHom,
        galCp_apply]
      exact AInf.fontaineTheta_gal_smul σ x)
  exact congrFun (congrArg DFunLike.coe h) y
end GroundTheory.PAdicHodge.ACris
