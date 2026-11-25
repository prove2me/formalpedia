-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:42.537967+00:00
-- url     : https://prove2.me/submissions/6d14c6ee-005a-4144-9dd6-f97891dfef5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution {k : ℕ} {x y : Ω} (h : Cong p k x y) : Cong p k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, IsIntegral.neg hz, by linear_combination -e⟩
end GlobalTheory.K5.Basic
