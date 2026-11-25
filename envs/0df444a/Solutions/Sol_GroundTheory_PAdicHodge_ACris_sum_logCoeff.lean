-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.sum_logCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:14.653442+00:00
-- url     : https://prove2.me/submissions/9824b2b8-3062-4a92-8360-33225deab1db

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_sum_powCoeff

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
omit hp
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), logCoeff p n j = (-1) ^ j * p * j.factorial :=
  sum_powCoeff p j
end GroundTheory.PAdicHodge.ACris
