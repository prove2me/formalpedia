-- Prove2me | solution 1 for GlobalTheory.BlockValue.OnlyIn.exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:45.584026+00:00
-- url     : https://prove2.me/submissions/6e8929fd-2f12-45a4-8735-4863823aa5d5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.BlockValue
namespace OnlyIn
theorem _root_.solution {S : σ → Prop} {f : MvPowerSeries σ C} (hf : OnlyIn S f) :
    OnlyIn S (mvExp f) := by
  intro m hm
  change ∑ k ∈ Finset.range (m.degree + 1), _ ≠ _ at hm
  obtain ⟨k, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  exact hf.pow k m (fun h => hne (by rw [h, zero_div]))
end OnlyIn
end GlobalTheory.BlockValue
