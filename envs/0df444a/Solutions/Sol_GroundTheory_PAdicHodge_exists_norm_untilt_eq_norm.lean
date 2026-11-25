-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_untilt_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:58.852514+00:00
-- url     : https://prove2.me/submissions/8cad967f-b3f8-4307-af36-24cc5033f05c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_norm_untilt_eq_norm_of_norm_le_one_ecbe03a01da8


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
theorem _root_.solution {y : K} (hy0 : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : 𝒪♭, ‖♮a‖ = ‖y‖ :=
  _root_.GroundTheory.Variant₂.N1.exists_norm_untilt_eq_norm_of_norm_le_one hy0 hy1
end GroundTheory.PAdicHodge
