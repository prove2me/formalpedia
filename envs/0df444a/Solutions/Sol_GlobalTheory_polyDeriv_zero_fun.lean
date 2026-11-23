-- Prove2me | solution 1 for GlobalTheory.polyDeriv_zero_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:41.418829+00:00
-- url     : https://prove2.me/submissions/57e70eb6-cbdb-4653-8a4d-b85250da2cef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_polyDerivLinear_apply
import Theorems.Thm_GlobalTheory_polyDeriv_zero
import Theorems.Thm_GlobalTheory_polyDeriv_monomial
import Theorems.Thm_GlobalTheory_polyDeriv_C
import Theorems.Thm_GlobalTheory_polyDeriv_one
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

set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (P : MvPolynomial ι 𝕜) (a : ι → 𝕜) :
    polyDeriv P (fun _ => (0 : V)) a = 0 := by
  simp [polyDeriv]
end GlobalTheory
