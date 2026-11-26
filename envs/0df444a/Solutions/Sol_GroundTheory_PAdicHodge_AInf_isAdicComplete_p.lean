-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.isAdicComplete_p
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:30:07.703065+00:00
-- url     : https://prove2.me/submissions/d9a96114-8a04-4065-8454-bd8e51c2eb0e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p

open GroundTheory.PAdicHodge.AInf in
theorem solution : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) :=
  WittVector.isAdicCompleteIdealSpanP
