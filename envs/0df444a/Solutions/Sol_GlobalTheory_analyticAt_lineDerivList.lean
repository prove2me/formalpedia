-- Prove2me | solution 1 for GlobalTheory.analyticAt_lineDerivList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:00.103126+00:00
-- url     : https://prove2.me/submissions/a0ca9050-5e20-40dd-95f6-78ec4c9baf2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_analyticAt_lineDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    AnalyticAt 𝕜 (lineDerivList 𝕜 l F) a := by
  induction l with
  | nil => exact h
  | cons v l ih => exact analyticAt_lineDeriv ih v
end GlobalTheory
