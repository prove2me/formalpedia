-- Prove2me | solution 1 for GlobalTheory.BlockValue.eq_zero_of_mapDomain_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:34.901172+00:00
-- url     : https://prove2.me/submissions/295cbe93-61d1-446a-80d5-6bbeac859872

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
theorem _root_.solution (π : σ → κ) {m : σ →₀ ℕ} (h : m.mapDomain π ≤ 0) : m = 0 := by
  have h0 : m.mapDomain π = 0 := le_antisymm h bot_le
  have := Finsupp.degree_mapDomain π m
  rw [h0, map_zero] at this
  exact (Finsupp.degree_eq_zero_iff m).mp this.symm
end GlobalTheory.BlockValue
