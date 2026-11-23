-- Prove2me | solution 1 for GlobalTheory.lineDerivList_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:24.535664+00:00
-- url     : https://prove2.me/submissions/adc6200b-bdda-4ec5-be1f-ffadec2ff488

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
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {𝕜}
namespace GlobalTheory
theorem _root_.solution (v : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 (v :: l) F = fun z => lineDeriv 𝕜 (lineDerivList 𝕜 l F) z v := rfl
end GlobalTheory
