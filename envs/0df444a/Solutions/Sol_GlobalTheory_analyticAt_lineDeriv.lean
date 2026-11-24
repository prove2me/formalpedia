-- Prove2me | solution 1 for GlobalTheory.analyticAt_lineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:17.472041+00:00
-- url     : https://prove2.me/submissions/61b14b70-cf78-43e1-bb91-495e425c31f9

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
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v : E) :
    AnalyticAt 𝕜 (fun z => lineDeriv 𝕜 F z v) a := by
  have h1 : AnalyticAt 𝕜 (fun z => fderiv 𝕜 F z v) a :=
    ((ContinuousLinearMap.apply 𝕜 V v).analyticAt _).comp h.fderiv
  refine h1.congr ?_
  filter_upwards [h.eventually_analyticAt] with z hz
  exact hz.differentiableAt.lineDeriv_eq_fderiv.symm
end GlobalTheory
