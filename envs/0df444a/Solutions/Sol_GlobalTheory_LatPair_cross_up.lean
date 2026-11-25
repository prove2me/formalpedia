-- Prove2me | solution 1 for GlobalTheory.LatPair.cross_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:40.317386+00:00
-- url     : https://prove2.me/submissions/52346b8a-feb7-47ae-bac4-d009a22f7055

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_cross_hasVal

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
theorem _root_.solution (q : Unif k) (P : Pair k n) (x : {x : Red P.lat // x ≠ 0}) :
    cross q (up P.lat q x) P = P.red x.1 := by
  have h := cross_hasVal q (P := P) (up_ker P.lat q x).symm ((up_hasVal_iff _ q x x.1.out).2 (Red.mk_out _))
  rw [q.smul_inv_smul] at h
  rw [h.unique (P.hasVal_fn _), ← P.red_mk, Red.mk_out]
end GlobalTheory.LatPair
