-- Prove2me | solution 1 for GlobalTheory.lineDerivList_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:59.464655+00:00
-- url     : https://prove2.me/submissions/08622c66-a7b9-408f-acef-4ca83f33d111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv

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
namespace GlobalTheory
theorem _root_.solution {F G : E → V} {a : E} (h : F =ᶠ[𝓝 a] G) (l : List E) :
    lineDerivList 𝕜 l F =ᶠ[𝓝 a] lineDerivList 𝕜 l G := by
  induction l with
  | nil => exact h
  | cons v l ih =>
    filter_upwards [ih.eventuallyEq_nhds] with z hz
    exact hz.lineDeriv_eq
end GlobalTheory
