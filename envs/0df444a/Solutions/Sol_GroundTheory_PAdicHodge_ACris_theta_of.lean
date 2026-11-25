-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:09.686977+00:00
-- url     : https://prove2.me/submissions/0c78d9be-c233-405a-ab14-51a94a753d4f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Theorems.Thm_GroundTheory_PAdicHodge_AdicCompletion_extendRingHom_of

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
theorem _root_.solution (y : ACrisZero K p) :
    theta K p (AdicCompletion.of _ _ y) = thetaZero K p y :=
  AdicCompletion.extendRingHom_of _ _ _ _ y
end GroundTheory.PAdicHodge.ACris
