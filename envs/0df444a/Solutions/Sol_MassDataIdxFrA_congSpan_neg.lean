-- Prove2me | solution 1 for MassDataIdxFrA.congSpan_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:30.497927+00:00
-- url     : https://prove2.me/submissions/4792041d-7ff8-42d8-9dbb-1dc6867edc49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
open Matrix
variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]
namespace MassDataIdxFrA
theorem _root_.solution (S : Set (ι → F)) (v : ι → F) : CongSpan O γ S (-v) ↔ CongSpan O γ S v := by
  have key : ∀ x, CongSpan O γ S x → CongSpan O γ S (-x) := by
    rintro x ⟨w, hw, z, hz, rfl⟩
    exact ⟨-w, neg_mem hw, -z, fun i => neg_mem (hz i), by rw [smul_neg, neg_add]⟩
  exact ⟨fun h => by simpa using key _ h, key v⟩
end MassDataIdxFrA
