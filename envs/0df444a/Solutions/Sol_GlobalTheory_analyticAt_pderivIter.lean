-- Prove2me | solution 1 for GlobalTheory.analyticAt_pderivIter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:37.655437+00:00
-- url     : https://prove2.me/submissions/5e5683f7-a8af-4d6f-829c-c085d8b50832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_analyticAt_lineDerivList


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
theorem _root_.solution {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α : ι →₀ ℕ) : AnalyticAt 𝕜 (pderivIter α F) a :=
  analyticAt_lineDerivList h _
end GlobalTheory
