-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:51.349814+00:00
-- url     : https://prove2.me/submissions/972d230c-a0be-4bf0-b307-3211d6da7340

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_zcoeff_incl_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_coeff_zero_le_of_mem_ker
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_zcoeff_incl_zero
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_le


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
theorem _root_.solution (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p}
    (hx : x ∈ RingHom.ker θ) : gn K p ρ (algebraMap (AInf K p) 𝔸 x) ≤ ρ := by
  rw [gn_algebraMap]
  refine gaussNorm_le fun n => ?_
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [(teichLift K p).zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact hρ0.le
  · rw [zcoeff_incl_zero, norm_algebraMap_preTilt, zpow_zero, mul_one]
    exact (norm_coeff_zero_le_of_mem_ker hx).trans hp0
  · calc _ ≤ 1 * ρ ^ n :=
          mul_le_mul_of_nonneg_right (norm_zcoeff_incl_le_one x n) (zpow_nonneg hρ0.le n)
      _ ≤ ρ := by
          rw [one_mul]
          exact (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (show (1 : ℤ) ≤ n by omega)).trans_eq
            (zpow_one ρ)
end GroundTheory.PAdicHodge.WittTilt
