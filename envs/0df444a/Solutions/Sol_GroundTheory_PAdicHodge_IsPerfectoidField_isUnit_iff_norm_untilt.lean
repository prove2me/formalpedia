-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_iff_norm_untilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:46:38.70482+00:00
-- url     : https://prove2.me/submissions/521af52a-ecfb-4449-8094-0a07a88db741

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_dvd_of_norm_untilt_le

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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "φ" => RingEquiv.symm (frobeniusEquiv (PreTilt (normInteger K) p) p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {x : 𝒪♭} : IsUnit x ↔ ‖((PreTilt.untilt x : 𝒪) : K)‖ = 1 := by
  constructor
  · intro h
    exact isUnit_iff_norm_eq_one.1 (h.map PreTilt.untilt)
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [untilt_zero, ZeroMemClass.coe_zero, norm_zero] at h
      exact zero_ne_one h
    refine isUnit_of_dvd_one (dvd_of_norm_untilt_le p hx ?_)
    rw [map_one, OneMemClass.coe_one, norm_one, h]
end GroundTheory.PAdicHodge.IsPerfectoidField
