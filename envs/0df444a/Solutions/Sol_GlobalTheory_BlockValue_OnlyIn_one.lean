-- Prove2me | solution 1 for GlobalTheory.BlockValue.OnlyIn.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:45.573205+00:00
-- url     : https://prove2.me/submissions/052a1f9d-1e33-499e-80c9-d3f870e23a26

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq

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
theorem _root_.solution (S : σ → Prop) : OnlyIn S (1 : MvPowerSeries σ C) := by
  classical
  intro m hm x hx
  rw [MvPowerSeries.coeff_one] at hm
  have : m = 0 := by by_contra h; simp [h] at hm
  simp [this] at hx
end OnlyIn
end GlobalTheory.BlockValue
