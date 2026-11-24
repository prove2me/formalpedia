-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.tr_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:57.825325+00:00
-- url     : https://prove2.me/submissions/66e65c5c-9b49-4f63-b3ac-3e9aeab02b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_tr_apply
import Theorems.Thm_P2M_GlobalTheory_LatPair_tr__apply_bf1204b7b27f


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
theorem _root_.solution {φ : Form k n M} (h : φ ∈ Mram k n M) : tr φ = 0 ∧ tr' φ = 0 :=
  ⟨funext fun P => (tr_apply φ P).trans (sum_stable_eq_zero h _ (by simp)),
    funext fun P => (tr'_apply φ P).trans (sum_stable_eq_zero h _ (by simp))⟩
end GlobalTheory.LatPair.Model
