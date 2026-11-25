-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_natCast_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:59.45035+00:00
-- url     : https://prove2.me/submissions/287a7650-d5ff-42cb-b326-740e8951be9f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gaussNorm_single_one
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_1768146d2888


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
theorem _root_.solution (hρ0 : 0 < ρ) : gn K p ρ (p : 𝔸) = ρ := by
  rw [← map_natCast (algebraMap (AInf K p) 𝔸) p, gn_algebraMap, map_natCast,
    show (p : WittVector p K♭) = (teichLift K p).π ^ 1 by rw [pow_one]; rfl,
    TeichLift.zcoeff_π_pow]
  exact_mod_cast gaussNorm_single_one hρ0
end GroundTheory.PAdicHodge.WittTilt
