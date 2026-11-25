-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.gal_smul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:48.099037+00:00
-- url     : https://prove2.me/submissions/8afe0785-274e-4311-a82c-f96834e158b3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_galCris_of

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
    σ • AdicCompletion.of (Ideal.span {(p : ACrisZero ℂ_[p] p)}) _ y =
      AdicCompletion.of _ _ (σ • y) :=
  galCris_of σ y
end GroundTheory.PAdicHodge.ACris
