-- Prove2me | solution 1 for GlobalTheory.TorsionForm.wedge_contr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:26.69941+00:00
-- url     : https://prove2.me/submissions/437a2082-7b95-4331-98d7-fc7293657ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormPoint_049da9a0b6d9fde7
import Theorems.Thm_GlobalTheory_TorsionForm_sgn_mul_self
import Theorems.Thm_GlobalTheory_TorsionForm_sgn_erase
import Theorems.Thm_GlobalTheory_TorsionForm_sgn_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
open GlobalTheory GlobalTheory.TorsionForm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)
namespace GlobalTheory.TorsionForm
theorem _root_.solution {m : ℕ} (i : Fin m) (w : Ext m) :
    wedge i (contr i w) + contr i (wedge i w) = w := by
  funext S
  by_cases hS : i ∈ S
  · simp [wedge, contr, hS, sgn_erase, ← mul_assoc, sgn_mul_self, Finset.insert_erase hS]
  · simp [wedge, contr, hS, sgn_insert, ← mul_assoc, sgn_mul_self, Finset.erase_insert hS]
end GlobalTheory.TorsionForm
