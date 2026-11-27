-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normInteger_eq_valued_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:34.036351+00:00
-- url     : https://prove2.me/submissions/72b6d594-2337-471b-8eec-2630681f143f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField

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
open NNReal
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {K}
open scoped NormedField
namespace GroundTheory.PAdicHodge
theorem _root_.solution : normInteger K = Valued.integer K := rfl
end GroundTheory.PAdicHodge
