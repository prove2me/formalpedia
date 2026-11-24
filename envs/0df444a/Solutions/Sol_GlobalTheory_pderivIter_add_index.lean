-- Prove2me | solution 1 for GlobalTheory.pderivIter_add_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:52.762286+00:00
-- url     : https://prove2.me/submissions/6fb40a02-3ed8-40a6-9ffd-50ef9a6960c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_pderivList_append
import Theorems.Thm_GlobalTheory_polyDerivLinear_apply
import Theorems.Thm_GlobalTheory_polyDeriv_zero
import Theorems.Thm_GlobalTheory_polyDeriv_monomial
import Theorems.Thm_GlobalTheory_polyDeriv_C
import Theorems.Thm_GlobalTheory_polyDeriv_one
import Theorems.Thm_GlobalTheory_polyDeriv_zero_fun
import Theorems.Thm_GlobalTheory_pderivList_perm
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


attribute [local simp] GlobalTheory.polyDerivLinear_apply
attribute [local simp] GlobalTheory.polyDeriv_zero
attribute [local simp] GlobalTheory.polyDeriv_monomial
attribute [local simp] GlobalTheory.polyDeriv_C
attribute [local simp] GlobalTheory.polyDeriv_one
attribute [local simp] GlobalTheory.polyDeriv_zero_fun

set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α β : ι →₀ ℕ) : pderivIter (α + β) F a = pderivIter α (pderivIter β F) a := by
  rw [pderivIter, pderivIter, pderivIter, ← pderivList_append]
  refine pderivList_perm h ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [Multiset.coe_toList, map_add]
end GlobalTheory
