-- Prove2me | solution 1 for GlobalTheory.pderivList_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:17.313665+00:00
-- url     : https://prove2.me/submissions/a646e8d8-91fc-4cb2-b025-d0dda393ec13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_lineDerivList_perm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List ι}
    (hl : l₁.Perm l₂) : pderivList l₁ F a = pderivList l₂ F a :=
  lineDerivList_perm h (hl.map _)
end GlobalTheory
