-- Prove2me | solution 2 for GroundTheory.PAdicHodge.ACris.theta_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:02.698592+00:00
-- url     : https://prove2.me/submissions/f31c38b8-cc5f-44c4-a58a-bbd30dbd1b09

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_fontaineTheta


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
theorem _root_.solution : Function.Surjective (theta K p) := fun y => by
  obtain ⟨x, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) p y
  exact ⟨_, theta_algebraMap x⟩
end GroundTheory.PAdicHodge.ACris
