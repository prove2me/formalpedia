-- Prove2me | solution 1 for GlobalTheory.AdaptedExp.eventually_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:28.67031+00:00
-- url     : https://prove2.me/submissions/2e3d224f-a5de-4ff5-a957-ab307ef0a428

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAdaptedExponentSchwartzBruhatLastColumn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.AdaptedExp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.AdaptedExp
theorem _root_.solution {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le
end GlobalTheory.AdaptedExp
