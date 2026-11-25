-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.tcoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:18.471503+00:00
-- url     : https://prove2.me/submissions/4474c129-2a74-459c-a6d4-216209cfd37b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
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


attribute [local simp] GroundTheory.PAdicHodge.WittTilt.teichLift_π

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (x : AInf K p) : tcoeff x 0 = x.coeff 0 := by
  simp [tcoeff]
end GroundTheory.PAdicHodge.WittTilt
