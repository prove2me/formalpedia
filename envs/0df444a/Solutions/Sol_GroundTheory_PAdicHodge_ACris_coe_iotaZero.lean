-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.coe_iotaZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:42.358282+00:00
-- url     : https://prove2.me/submissions/4549effe-fab7-4d2b-a4d9-1853bdf65237

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR

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
    (iotaZero K p m y : 𝔸 ⧸ kerAway K p ^ m) = Ideal.Quotient.mk (kerAway K p ^ m) (y : 𝔸) :=
  rfl
end GroundTheory.PAdicHodge.ACris
