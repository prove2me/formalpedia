-- Prove2me | solution 1 for GlobalTheory.lineDerivList_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:25:46.541057+00:00
-- url     : https://prove2.me/submissions/24034275-acd3-456c-98e2-1d70feb0cceb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_lineDerivList_eq_iteratedFDeriv

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
theorem _root_.solution {F G : E → V} {a : E} (hF : AnalyticAt 𝕜 F a) (hG : AnalyticAt 𝕜 G a)
    (l : List E) :
    lineDerivList 𝕜 l (fun z => F z + G z) a
      = lineDerivList 𝕜 l F a + lineDerivList 𝕜 l G a := by
  have hFG : AnalyticAt 𝕜 (fun z => F z + G z) a := hF.add hG
  rw [lineDerivList_eq_iteratedFDeriv hFG, lineDerivList_eq_iteratedFDeriv hF,
    lineDerivList_eq_iteratedFDeriv hG,
    fun_iteratedFDeriv_add_apply (hF.contDiffAt) (hG.contDiffAt)]
  rfl
end GlobalTheory
