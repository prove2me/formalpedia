-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_preTiltEquivNormInteger
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:42.319172+00:00
-- url     : https://prove2.me/submissions/da4d52cc-c0e3-4b91-a162-afdca5ce8408

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField

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
theorem _root_.solution (a : 𝒪♭) :
    ‖((preTiltEquivNormInteger K p a : normInteger K♭) : K♭)‖ = ‖a‖ := by
  rw [coe_preTiltEquivNormInteger, norm_algebraMap_preTilt]
end GroundTheory.PAdicHodge
