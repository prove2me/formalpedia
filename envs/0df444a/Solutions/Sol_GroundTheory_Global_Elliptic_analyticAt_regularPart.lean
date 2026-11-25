-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_regularPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:32.300055+00:00
-- url     : https://prove2.me/submissions/4d4e1b61-fbe3-4144-a81a-9e562bc24bfa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_dslopeIter
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_laurentNumerator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (regularPart f p) p :=
  analyticAt_dslopeIter (analyticAt_laurentNumerator hf) _
end GroundTheory.Global.Elliptic
