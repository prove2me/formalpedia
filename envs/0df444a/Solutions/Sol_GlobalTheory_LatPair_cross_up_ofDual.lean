-- Prove2me | solution 1 for GlobalTheory.LatPair.cross_up_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:05.4471+00:00
-- url     : https://prove2.me/submissions/82ca4684-33bd-4a45-a06e-db48ddf69ebf

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
theorem _root_.solution (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (x : {x : Red L // x ≠ 0})
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : cross q (up L q x) (ofDual L f) = f.1 x.1 := by
  have h := cross_hasVal q (P := ofDual L f) (up_ker L q x).symm ((up_hasVal_iff _ q x x.1.out).2 (Red.mk_out _))
  rw [q.smul_inv_smul] at h
  rw [h.unique (ofDual_hasVal L f _), Red.mk_out]
end GlobalTheory.LatPair
