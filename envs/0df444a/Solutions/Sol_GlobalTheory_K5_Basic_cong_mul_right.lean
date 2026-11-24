-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:51.223869+00:00
-- url     : https://prove2.me/submissions/85fafb2d-bf27-4a60-a85f-60156f5db155

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
theorem _root_.solution {k : ℕ} {x y c : Ω} (h : Cong p k x y) (hc : IsInt p c) :
    Cong p k (x * c) (y * c) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a * c, IsIntegral.mul ha hc, by linear_combination c * e⟩
end GlobalTheory.K5.Basic
