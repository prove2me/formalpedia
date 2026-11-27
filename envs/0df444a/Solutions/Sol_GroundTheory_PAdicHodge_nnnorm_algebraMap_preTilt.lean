-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nnnorm_algebraMap_preTilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:31.725718+00:00
-- url     : https://prove2.me/submissions/d282ab4c-37e4-474d-a6cd-8967f204f3bc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Theorems.Thm_GroundTheory_PAdicHodge_nnnorm_eq_val


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
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)
namespace GroundTheory.PAdicHodge
theorem _root_.solution (a : 𝒪♭) : ‖algebraMap 𝒪♭ K♭ a‖₊ =
    PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p a := by
  rw [← nnnorm_eq_val]
  exact NNReal.eq (norm_algebraMap_preTilt a)
end GroundTheory.PAdicHodge
