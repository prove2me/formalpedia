-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:17.799897+00:00
-- url     : https://prove2.me/submissions/4b4a2acb-6289-45aa-a457-73cd32a65608

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
theorem _root_.solution {k : ℕ} {x y z : Ω} (h : Cong p k x y) (h' : Cong p k y z) : Cong p k x z := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a + b, IsIntegral.add ha hb, by linear_combination e + e'⟩
end GlobalTheory.K5.Basic
