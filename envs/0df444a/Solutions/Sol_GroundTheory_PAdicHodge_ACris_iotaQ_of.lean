-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.iotaQ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:10.54808+00:00
-- url     : https://prove2.me/submissions/6c533baf-7fa7-4dae-bfce-00ddb4e60eb8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Theorems.Thm_GroundTheory_PAdicHodge_AdicCompletion_extendRingHom_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (m : ℕ) (y : ACrisZero K p) :
    iotaQ K p m (_root_.AdicCompletion.of _ _ y) = Ideal.Quotient.mk (kerAway K p ^ m) (y : 𝔸) := by
  rw [iotaQ, RingHom.comp_apply, embedding₂, AdicCompletion.extendRingHom_of]
  rfl
end GroundTheory.PAdicHodge.ACris
