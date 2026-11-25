-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.norm_coeff_incl_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:40.622196+00:00
-- url     : https://prove2.me/submissions/e5d4830b-de79-4e61-b7c4-a7262c3fdac2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_incl_mem_int
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_int_iff


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
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (x : AInf K p) (n : ℕ) : ‖(teichLift K p).coeff (incl K p x) n‖ ≤ 1 :=
  (teichLift K p).mem_int_iff.1 (incl_mem_int x) n
end GroundTheory.PAdicHodge.WittTilt
