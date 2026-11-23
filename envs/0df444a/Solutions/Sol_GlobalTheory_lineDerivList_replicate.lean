-- Prove2me | solution 1 for GlobalTheory.lineDerivList_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:46.761765+00:00
-- url     : https://prove2.me/submissions/1befd9e2-81bc-4fa7-94aa-23b9d1df6d8c

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
theorem _root_.solution (n : ℕ) (v : E) (F : E → V) (z : E) (t : 𝕜) :
    lineDerivList 𝕜 (List.replicate n v) F (z + t • v)
      = iteratedDeriv n (fun s : 𝕜 => F (z + s • v)) t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, lineDerivList_cons, iteratedDeriv_succ]
    simp only [lineDeriv, add_assoc, ← add_smul, ih]
    rw [deriv_comp_const_add (f := iteratedDeriv n (fun s : 𝕜 => F (z + s • v))), add_zero]
end GlobalTheory
