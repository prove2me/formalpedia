-- Prove2me | solution 1 for GlobalTheory.LatPair.cross_dia_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:30.248083+00:00
-- url     : https://prove2.me/submissions/d3d03c64-1ee0-40c4-9b80-029c9d3ba092

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
theorem _root_.solution (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q P₁ (c • P) = c * cross q P₁ P := by
  have h1 := Pair.dia_hasVal.1 (cross_hasVal q (P := c • P) h P₁.hasVal_vec)
  rw [← h1.unique (cross_hasVal q h P₁.hasVal_vec), Units.mul_inv_cancel_left]
end GlobalTheory.LatPair
