-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:34.958198+00:00
-- url     : https://prove2.me/submissions/a5d9c0a8-813e-43fa-aa02-e96ab3966329

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_convergesAt_zcoeff_incl
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_exists_toB_mul
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_eq_zero_of_mul_pow
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_incl_injective
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_toB_injective


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
theorem _root_.solution (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z : 𝔸} (hz : z ≠ 0) : 0 < gn K p ρ z := by
  obtain ⟨M, x, h⟩ := exists_toB_mul z
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at h
    exact hz (toB_injective (by rw [map_zero]; exact (teichLift K p).eq_zero_of_mul_pow h))
  have hx' : (teichLift K p).zcoeff (incl K p x) ≠ 0 := fun h0 =>
    hx (incl_injective (by rw [((teichLift K p).zcoeff_eq_zero_iff _).1 h0, map_zero]))
  have hc := convergesAt_zcoeff_incl x hρ0 hρ1
  unfold gn
  rw [TeichLift.coeffB_eq _ h, gaussNorm_shift hρ0]
  exact mul_pos (gaussNorm_pos hρ0 hc hx') (zpow_pos hρ0 _)
end GroundTheory.PAdicHodge.WittTilt
