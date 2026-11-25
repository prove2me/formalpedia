-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.iota_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:29.230342+00:00
-- url     : https://prove2.me/submissions/d08c120a-ad17-49d2-8abe-2e891bde89d4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_iotaQ_of
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947

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
theorem _root_.solution (y : ACrisZero K p) :
    iota K p (_root_.AdicCompletion.of _ _ y) = toBDeRhamPlus (normInteger K) p (y : 𝔸) := by
  apply _root_.AdicCompletion.ext_evalₐ
  intro m
  rw [evalₐ_iota, iotaQ_of]
  exact (_root_.AdicCompletion.evalₐ_of _ m (y : 𝔸)).symm
end GroundTheory.PAdicHodge.ACris
