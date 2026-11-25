-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.logCoeff_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:28.744615+00:00
-- url     : https://prove2.me/submissions/5fafc421-ae54-4a06-81de-1003d4549dc2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_powCoeff_of_gt

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
theorem _root_.solution {n j : ℕ} (h : p * (n + 1) < j + 1) : logCoeff p n j = 0 := by
  simp [logCoeff, powCoeff_of_gt p h]
end GroundTheory.PAdicHodge.ACris
