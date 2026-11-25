-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.convergesAt_toB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:19.090798+00:00
-- url     : https://prove2.me/submissions/821c3eed-0a33-442d-9383-6681cd7e5d61

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_convergesAt_zcoeff_incl
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_exists_toB_mul

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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (z : 𝔸) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt ((teichLift K p).coeffB (toB K p z)) ρ := by
  obtain ⟨M, x, h⟩ := exists_toB_mul z
  rw [TeichLift.coeffB_eq _ h]
  exact convergesAt_shift hρ0 (convergesAt_zcoeff_incl x hρ0 hρ1) M
end GroundTheory.PAdicHodge.WittTilt
