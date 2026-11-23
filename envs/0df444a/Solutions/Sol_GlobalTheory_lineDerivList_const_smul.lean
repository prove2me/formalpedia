-- Prove2me | solution 1 for GlobalTheory.lineDerivList_const_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:37.187415+00:00
-- url     : https://prove2.me/submissions/2f625918-ebc5-4875-b555-f89569a7d1dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil

set_option autoImplicit false
open Filter Topology
open scoped ContDiff
open GlobalTheory
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {𝕜}
namespace GlobalTheory
theorem _root_.solution (l : List E) (c : 𝕜) (F : E → V) :
    lineDerivList 𝕜 l (fun z => c • F z) = fun z => c • lineDerivList 𝕜 l F z := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv]
    exact deriv_fun_const_smul_field c _
end GlobalTheory
