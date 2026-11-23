-- Prove2me | solution 1 for GlobalTheory.SatakeFlip.inv_diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:33.212613+00:00
-- url     : https://prove2.me/submissions/5ac21743-240b-47b0-b445-92fc8455469b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Theorems.Thm_GlobalTheory_SmGL_mem_borel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix
open GlobalTheory GlobalTheory.SatakeFlip
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.SatakeFlip
theorem _root_.solution {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) (i : Fin n) :
    (b⁻¹).val i i * b.val i i = 1 := by
  have h := congrFun (congrFun (Units.inv_mul b) i) i
  rw [mul_apply, one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h' | h'
    · rw [(mem_borel R).1 (inv_mem hb) _ _ h', zero_mul]
    · rw [(mem_borel R).1 hb _ _ h', mul_zero]
  · simp
end GlobalTheory.SatakeFlip
