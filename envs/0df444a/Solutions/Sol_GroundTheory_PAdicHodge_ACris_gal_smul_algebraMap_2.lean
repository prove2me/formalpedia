-- Prove2me | solution 2 for GroundTheory.PAdicHodge.ACris.gal_smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:17.499547+00:00
-- url     : https://prove2.me/submissions/b036f463-9aad-4fe6-9ba4-e80c8bde46f1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_gal_smul_algebraMap_zero
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_gal_smul_of

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
    σ • algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) x =
      algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (σ • x) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, gal_smul_of,
    gal_smul_algebraMap_zero]
end GroundTheory.PAdicHodge.ACris
