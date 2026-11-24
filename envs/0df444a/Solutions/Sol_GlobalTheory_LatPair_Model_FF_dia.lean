-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.FF_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:53:23.733052+00:00
-- url     : https://prove2.me/submissions/aabd6b22-f2ff-47b2-a866-5d857f92734a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_withLat_dia
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_left
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_right


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
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (c : 𝓀[k]ˣ) (φ : Form k n M) :
    FF q χ (dia c φ) = dia c (FF q χ φ) := by
  ext P₁
  simp only [FF_apply, dia_apply, Pair.dia_ker]
  rw [← sum_withLat_dia c _ fun P => χ (cross q (c • P₁) P) • φ P]
  refine Finset.sum_congr rfl fun P hP => ?_
  have h := mem_withLat.1 hP
  rw [cross_dia_left q (P := c • P) h, cross_dia_right q h, Units.inv_mul_cancel_left]
end GlobalTheory.LatPair.Model
