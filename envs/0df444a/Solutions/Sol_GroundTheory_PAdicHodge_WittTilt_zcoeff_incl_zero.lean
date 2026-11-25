-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.zcoeff_incl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:32.666369+00:00
-- url     : https://prove2.me/submissions/6ed3d823-f0f4-4699-a48e-8fd5625cf17e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_zcoeff_incl_natCast
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_tcoeff_zero


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
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (x : AInf K p) :
    (teichLift K p).zcoeff (incl K p x) 0 = algebraMap 𝒪♭ K♭ (x.coeff 0) := by
  have := zcoeff_incl_natCast x 0
  rwa [tcoeff_zero, Nat.cast_zero] at this
end GroundTheory.PAdicHodge.WittTilt
