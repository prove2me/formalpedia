-- Prove2me | solution 1 for GlobalTheory.T.schwartz_compact_support_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:36.484665+00:00
-- url     : https://prove2.me/submissions/f1d7a5c8-7c72-469d-bf44-505a6bf1394a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCompactSupportDense
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCompactSupportDenseStatement
import Theorems.Thm_GlobalTheory_schwartz_mem_closure_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  first | exact @GlobalTheory.schwartz_mem_closure_hasCompactSupport | exact GlobalTheory.schwartz_mem_closure_hasCompactSupport | (intros; apply GlobalTheory.schwartz_mem_closure_hasCompactSupport <;> assumption)
end _root_.GlobalTheory.T
