-- Prove2me | solution 1 for GlobalTheory.LatPair.cross_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:23.979075+00:00
-- url     : https://prove2.me/submissions/70e6e2ed-cdfa-4e5a-ac0f-88ae072d76f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_cross_hasVal
import Theorems.Thm_GlobalTheory_LatPair_Pair_HasVal_gl_smul

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
variable [Fintype n] [DecidableEq n]
namespace GlobalTheory.LatPair
theorem _root_.solution (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (g : GL n k) :
    cross q (g • P₁) (g • P) = cross q P₁ P := by
  have h1 := cross_hasVal q (P₁ := g • P₁) (P := g • P) (by simp [h]) (P₁.hasVal_vec.gl_smul g)
  rw [← smul_comm g] at h1
  exact h1.unique ((cross_hasVal q h P₁.hasVal_vec).gl_smul g)
end GlobalTheory.LatPair
