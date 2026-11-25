-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.convergesAt_zcoeff_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:24.342699+00:00
-- url     : https://prove2.me/submissions/2c81fcc6-44be-4157-8dba-e3ef9d0e81cb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_zcoeff_incl_le_one

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
theorem _root_.solution (x : AInf K p) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt ((teichLift K p).zcoeff (incl K p x)) ρ := by
  refine convergesAt_of_eventually hρ0 ((teichLift K p).zcoeff_neg_exists _) fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨N, fun n hn => ?_⟩
  calc ‖(teichLift K p).zcoeff (incl K p x) n‖ * ρ ^ n ≤ 1 * ρ ^ (N : ℤ) :=
        mul_le_mul (norm_zcoeff_incl_le_one x n) (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le hn)
          (zpow_pos hρ0 n).le zero_le_one
    _ ≤ ε := by rw [one_mul, zpow_natCast]; exact hN.le
end GroundTheory.PAdicHodge.WittTilt
