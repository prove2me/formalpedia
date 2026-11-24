-- Prove2me | solution 1 for GlobalTheory.TorsionForm.sgn_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:54.843909+00:00
-- url     : https://prove2.me/submissions/27ced86b-56d3-4561-88b8-5069ad3a38aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormPoint_049da9a0b6d9fde7
import Theorems.Thm_GlobalTheory_TorsionForm_sgn_erase

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
theorem _root_.solution {m : ℕ} (i : Fin m) (S : Finset (Fin m)) : sgn i (insert i S) = sgn i S := by
  rw [← sgn_erase, Finset.erase_insert_eq_erase, sgn_erase]
end GlobalTheory.TorsionForm
