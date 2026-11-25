-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.exists_toB_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:23.053875+00:00
-- url     : https://prove2.me/submissions/9ea74de5-a8f3-443f-a862-91abb144d778

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_toB_algebraMap


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
theorem _root_.solution (z : 𝔸) : ∃ (M : ℕ) (x : AInf K p),
    toB K p z * algebraMap _ (teichLift K p).B (teichLift K p).π ^ M =
      algebraMap _ (teichLift K p).B (incl K p x) := by
  obtain ⟨M, x, hx⟩ := IsLocalization.Away.surj (p : AInf K p) z
  refine ⟨M, x, ?_⟩
  have h := congrArg (toB K p) hx
  rw [map_mul, map_pow, toB_algebraMap, toB_algebraMap, map_natCast, map_natCast] at h
  rw [show algebraMap (WittVector p K♭) (teichLift K p).B (teichLift K p).π = (p : (teichLift K p).B) from
    map_natCast _ p]
  exact h
end GroundTheory.PAdicHodge.WittTilt
