-- Prove2me | solution 1 for GlobalTheory.BlockValue.Lead.of_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:09.603804+00:00
-- url     : https://prove2.me/submissions/90d62f21-fd46-48b3-8f7a-1f05b33d3c18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_BlockValue_eq_zero_of_mapDomain_le

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
namespace Lead
theorem _root_.solution (π : σ → κ) {f : MvPowerSeries σ C} (h : MvPowerSeries.coeff 0 f = 1) :
    Lead π 0 f := by
  refine ⟨fun m _ => ?_, h⟩
  rw [Finsupp.mapDomain_zero]
  exact ⟨bot_le, eq_zero_of_mapDomain_le π⟩
end Lead
end GlobalTheory.BlockValue
