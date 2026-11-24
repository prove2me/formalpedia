-- Prove2me | solution 1 for GlobalTheory.lineDerivList_map_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:02.294147+00:00
-- url     : https://prove2.me/submissions/969d84e9-8d66-4c0e-8d80-d81240533adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_cons
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
open scoped ContDiff
open GlobalTheory
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {𝕜}
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (c : κ → 𝕜) (e : κ → E) (l : List κ) (F : E → V) :
    lineDerivList 𝕜 (l.map fun k => c k • e k) F
      = fun z => (l.map c).prod • lineDerivList 𝕜 (l.map e) F z := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext z
    simp only [List.map_cons, lineDerivList_cons, ih, lineDeriv_smul, List.prod_cons, mul_smul]
    congr 1
    simp only [lineDeriv]
    exact deriv_fun_const_smul_field _ _
end GlobalTheory
