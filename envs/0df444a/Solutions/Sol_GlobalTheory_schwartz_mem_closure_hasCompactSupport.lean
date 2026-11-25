-- Prove2me | solution 1 for GlobalTheory.schwartz_mem_closure_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:33.592056+00:00
-- url     : https://prove2.me/submissions/b1bfae78-aa1b-432c-ae6c-556747db96f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDenseHasCompactSupport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCompactSupportDense
import Theorems.Thm_GlobalTheory_schwartz_dense_hasCompactSupport


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  intro V _ _ _ f
  exact schwartz_dense_hasCompactSupport f
end GlobalTheory
