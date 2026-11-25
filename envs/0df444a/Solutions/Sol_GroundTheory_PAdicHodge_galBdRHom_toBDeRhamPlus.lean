-- Prove2me | solution 1 for GroundTheory.PAdicHodge.galBdRHom_toBDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:34.600802+00:00
-- url     : https://prove2.me/submissions/1903855a-d5be-474e-83ac-baf16af15ff9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_evalB_toBDeRhamPlus

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
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝒪" => normInteger ℂ_[p]
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger ℂ_[p]) p))
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (a : 𝔸) :
    galBdRHom σ (toBDeRhamPlus 𝒪 p a) = toBDeRhamPlus 𝒪 p (galAway σ a) := by
  refine IsPerfectoidField.evalB_ext fun n => ?_
  rw [evalB_galBdRHom, IsPerfectoidField.evalB_toBDeRhamPlus,
    IsPerfectoidField.evalB_toBDeRhamPlus, galQuot_mk]
end GroundTheory.PAdicHodge
