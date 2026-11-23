-- Prove2me | solution 1 for GlobalTheory.LatPair.cross_hasVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:17.07407+00:00
-- url     : https://prove2.me/submissions/a5e0059d-56a2-4c25-8bc8-2c3e828a293b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_Pair_hasVal_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
namespace GlobalTheory.LatPair
theorem _root_.solution (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) {e : n → k} (he : P₁.HasVal e 1) :
    P.HasVal (q.1 • e) (cross q P₁ P) := by
  have h1 : q.1 • P₁.vec ∈ P.lat := h ▸ Pair.smul_mem_ker q.mem_max P₁.hasVal_vec.mem
  have h2 : q.1 • (e - P₁.vec) ∈ P.ker := Pair.smul_mem_ker q.mem_max (h ▸ Pair.sub_vec_mem he)
  simpa [smul_sub, cross] using (Pair.mem_ker.1 h2).add (Pair.hasVal_ev h1)
end GlobalTheory.LatPair
