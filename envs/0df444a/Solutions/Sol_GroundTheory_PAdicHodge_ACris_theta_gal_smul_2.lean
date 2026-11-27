-- Prove2me | solution 2 for GroundTheory.PAdicHodge.ACris.theta_gal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:50:54.392878+00:00
-- url     : https://prove2.me/submissions/35b0bae6-e518-4119-972a-0b458d6d75e4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_galCris_of
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_thetaZero_gal_smul
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_of
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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    ((theta ℂ_[p] p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((theta ℂ_[p] p x : normInteger ℂ_[p]) : ℂ_[p]) := by
  have h : (theta ℂ_[p] p).comp (galCris σ) =
      (integerMap (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)).comp
        (theta ℂ_[p] p) :=
    ringHom_ext fun y => by
      apply Subtype.ext
      rw [RingHom.comp_apply, RingHom.comp_apply, galCris_of, theta_of, theta_of,
        coe_integerMap, thetaZero_gal_smul]
      rfl
  have h' := congrArg (fun f => ((f x : normInteger ℂ_[p]) : ℂ_[p])) h
  simp only [RingHom.comp_apply, coe_integerMap] at h'
  exact h'
end GroundTheory.PAdicHodge.ACris
