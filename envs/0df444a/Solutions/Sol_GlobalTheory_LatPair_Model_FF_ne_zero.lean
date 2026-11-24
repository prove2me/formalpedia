-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.FF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:04.11714+00:00
-- url     : https://prove2.me/submissions/9f8e2ac4-6bb9-49b0-afc3-434866a97bde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_FFStar_FF
import Theorems.Thm_GlobalTheory_LatPair_Model_tr_eq_zero

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
theorem _root_.solution [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) {φ : Form k n M}
    (h : φ ∈ Mram k n M) (h0 : FF q χ φ = 0) : φ = 0 := by
  have := FFStar_FF q hχ φ
  rw [h0, map_zero, (tr_eq_zero h).1, sub_zero] at this
  refine (smul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ ?_)
  exact_mod_cast (Nat.card_pos (α := 𝓀[k])).ne'
end GlobalTheory.LatPair.Model
