-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_p_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:09.998809+00:00
-- url     : https://prove2.me/submissions/33179cd0-c0e4-4c1b-bb82-91dab9f26fa1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_mul
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_natCast_p
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_pow


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
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (z : 𝔸) :
    gn K p ρ ((p : 𝔸) ^ N * z) = ρ ^ N * gn K p ρ z := by
  rw [gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_natCast_p hρ0]
end GroundTheory.PAdicHodge.WittTilt
