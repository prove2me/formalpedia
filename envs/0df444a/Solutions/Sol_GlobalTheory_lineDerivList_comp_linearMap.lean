-- Prove2me | solution 1 for GlobalTheory.lineDerivList_comp_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:46.821575+00:00
-- url     : https://prove2.me/submissions/d5a6668a-8c02-4d73-8e32-2b4353d1348c

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
theorem _root_.solution {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (L : E' →ₗ[𝕜] E) (l : List E') (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (L z)) = fun z => lineDerivList 𝕜 (l.map L) F (L z) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, List.map_cons, map_add, map_smul]
end GlobalTheory
