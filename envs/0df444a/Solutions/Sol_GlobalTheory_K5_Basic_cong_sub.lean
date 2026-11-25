-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:41.159383+00:00
-- url     : https://prove2.me/submissions/b6d63da7-75a3-4e0f-bcdb-6c6edb90f2c0

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
theorem _root_.solution {k : ℕ} {x y x' y' : Ω} (h : Cong p k x y) (h' : Cong p k x' y') :
    Cong p k (x - x') (y - y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a - b, IsIntegral.sub ha hb, by linear_combination e - e'⟩
end GlobalTheory.K5.Basic
