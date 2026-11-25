-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.p_mul_logTermZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:13.219937+00:00
-- url     : https://prove2.me/submissions/665fdf97-a350-47c5-b8f3-d5b217979063

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_sum_logCoeff

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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {x : AInf K p}
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (hx : x ∈ RingHom.ker θ) (j : ℕ) :
    (p : ACrisZero K p) * logTermZero hx j =
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_logCoeff, logTermZero]
  push_cast
  ring
end GroundTheory.PAdicHodge.ACris
