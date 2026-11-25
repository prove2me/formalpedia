-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.norm_zcoeff_incl_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:10.573615+00:00
-- url     : https://prove2.me/submissions/0b1450d0-fa4f-4273-94c4-f4eea69c8ee8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_coeff_incl_le_one
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
attribute [local simp] P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65



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
theorem _root_.solution (x : AInf K p) (n : ℤ) :
    ‖(teichLift K p).zcoeff (incl K p x) n‖ ≤ 1 := by
  unfold TeichLift.zcoeff
  split_ifs
  · exact norm_coeff_incl_le_one x _
  · simp
end GroundTheory.PAdicHodge.WittTilt
