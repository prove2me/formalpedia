-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.span_p_pow_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:05.115842+00:00
-- url     : https://prove2.me/submissions/d145bf4b-2eab-4b25-97e5-e68b71fca975

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj

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
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (k : ℕ) :
    (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p)) =
      Ideal.span {(p : ACris K p)} ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
end GroundTheory.PAdicHodge.ACris
