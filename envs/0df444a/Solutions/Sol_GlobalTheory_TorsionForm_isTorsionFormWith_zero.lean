-- Prove2me | solution 1 for GlobalTheory.TorsionForm.isTorsionFormWith_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:24.498876+00:00
-- url     : https://prove2.me/submissions/4b089e57-5dff-44c2-9b75-cfbf80bcee9c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TranslationInv_27ddeabb7aac02dc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormWithPoint_2137add7c40a5a9d

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
open scoped Real ContDiff ComplexConjugate
open GlobalTheory GlobalTheory.TorsionForm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)
namespace GlobalTheory.TorsionForm
theorem _root_.solution (b : E) (T : Ext (n + n)) :
    IsTorsionFormWith τ M j h β b 0 T ↔ IsTorsionForm τ M j h β b T := by
  simp [IsTorsionFormWith, IsTorsionForm, IsHeatTraceWith, IsHeatTrace, baseMul]
end GlobalTheory.TorsionForm
