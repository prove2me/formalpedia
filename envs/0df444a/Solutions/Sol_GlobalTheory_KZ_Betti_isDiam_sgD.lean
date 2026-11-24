-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.isDiam_sgD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:05.278979+00:00
-- url     : https://prove2.me/submissions/a3fea9d3-8303-4daf-a595-77695ec00464

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
import Theorems.Thm_GlobalTheory_KZ_Betti_exists_isDiam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti
namespace GlobalTheory.KZ.Betti
theorem _root_.solution {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  exact Classical.epsilon_spec (exists_isDiam hN hl hd)
end GlobalTheory.KZ.Betti
