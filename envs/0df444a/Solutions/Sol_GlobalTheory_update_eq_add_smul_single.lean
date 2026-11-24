-- Prove2me | solution 1 for GlobalTheory.update_eq_add_smul_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:25.255673+00:00
-- url     : https://prove2.me/submissions/76a37b8c-b9d6-43ed-a85d-48a6b7373efe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (z : ι → 𝕜) (k : ι) (t : 𝕜) :
    Function.update z k t = z + (t - z k) • (Pi.single k 1 : ι → 𝕜) := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]
end GlobalTheory
