-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.isDiam_sgD_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:56:19.785992+00:00
-- url     : https://prove2.me/submissions/0eef05d9-10ff-41a6-baa8-ab7ead23b486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
import Theorems.Thm_GlobalTheory_KZ_Betti_isDiam_sgD

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
theorem _root_.solution {N l q : ℕ} (h : admitted N l (Letter.T q)) : IsDiam N l q (sgD N l q) := by
  have h' : q.Prime ∧ ¬ q ∣ N * l := h
  obtain ⟨hq, hqN⟩ := h'
  have hN : N ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  have hl : l ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  exact isDiam_sgD hN hl ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h'' => hqN (h''.mul_right l))
end GlobalTheory.KZ.Betti
