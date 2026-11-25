-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_smul_wittToBDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:14.233831+00:00
-- url     : https://prove2.me/submissions/96403d6f-4d38-47ae-8003-2160676f03d9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_toBDeRhamPlus

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (w : 𝕎𝒪♭) :
    σ • wittToBDeRhamPlus 𝒪 p w = wittToBDeRhamPlus 𝒪 p (σ • w) := by
  change σ • toBDeRhamPlus 𝒪 p (algebraMap 𝕎𝒪♭ 𝔸 w) = toBDeRhamPlus 𝒪 p (algebraMap 𝕎𝒪♭ 𝔸 (σ • w))
  rw [gal_smul_toBDeRhamPlus, galAway_algebraMap]
end GroundTheory.PAdicHodge
