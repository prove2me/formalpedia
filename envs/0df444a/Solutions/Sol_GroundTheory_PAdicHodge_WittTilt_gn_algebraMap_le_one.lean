-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_algebraMap_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:41.98457+00:00
-- url     : https://prove2.me/submissions/38b83a27-d285-46ec-8a86-493062375794

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_zcoeff_incl_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap
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
theorem _root_.solution (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (x : AInf K p) :
    gn K p ρ (algebraMap (AInf K p) 𝔸 x) ≤ 1 := by
  rw [gn_algebraMap]
  refine gaussNorm_le fun n => ?_
  by_cases hn : 0 ≤ n
  · exact mul_le_one₀ (norm_zcoeff_incl_le_one x n) (zpow_nonneg hρ0.le n)
      (zpow_le_one₀ hρ0 hρ1 hn)
  · rw [(teichLift K p).zcoeff_of_neg _ (not_le.1 hn), norm_zero, zero_mul]; exact zero_le_one
end GroundTheory.PAdicHodge.WittTilt
