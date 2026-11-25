-- Prove2me | solution 1 for GlobalTheory.K5.Basic.not_coboundary_constant_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:58:25.330307+00:00
-- url     : https://prove2.me/submissions/b5b138b0-28f9-4b8d-af62-0a078f352a15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_not_cong_one_zero

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
theorem _root_.solution (h : IsClo p Ω) {k : ℕ} (hk : k ≠ 0) (H : Subgroup (Gal p Ω)) :
    ¬ Cob1 k H (fun _ => (1 : Ω)) := by
  rintro ⟨x, -, hx⟩
  exact not_cong_one_zero h k hk (by simpa using hx 1 H.one_mem)
end GlobalTheory.K5.Basic
