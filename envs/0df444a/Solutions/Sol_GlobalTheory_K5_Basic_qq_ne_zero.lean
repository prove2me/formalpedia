-- Prove2me | solution 1 for GlobalTheory.K5.Basic.qq_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:40:03.633493+00:00
-- url     : https://prove2.me/submissions/36e8af7c-b193-4943-be05-fc1fd2f7d544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_isUnit_qO
import Theorems.Thm_GlobalTheory_K5_Basic_qq_pow

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
theorem _root_.solution (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h0 := qq_pow T n
  rw [h, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at h0
  exact ((isUnit_qO p).map (algebraMap (O0 p) Ω)).ne_zero h0.symm
end GlobalTheory.K5.Basic
