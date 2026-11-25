-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:26.917119+00:00
-- url     : https://prove2.me/submissions/a88ca8a9-99cf-48b1-b5c0-8d2741e36760

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_thetaZero_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_of

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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (x : AInf K p) :
    theta K p (algebraMap (AInf K p) (ACris K p) x) = θ x := by
  rw [AdicCompletion.algebraMap_apply, theta_of, thetaZero_algebraMap]
end GroundTheory.PAdicHodge.ACris
