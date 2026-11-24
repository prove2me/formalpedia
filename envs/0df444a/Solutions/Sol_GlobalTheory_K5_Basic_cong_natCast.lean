-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:58.351799+00:00
-- url     : https://prove2.me/submissions/801f893a-0538-46ab-87a3-d4f41a818d79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_isInt_intCast

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
theorem _root_.solution {k a b : ℕ} (h : a ≡ b [MOD p ^ k]) : Cong p k (a : Ω) (b : Ω) := by
  obtain ⟨c, hc⟩ := h.symm.dvd
  refine ⟨(c : Ω), isInt_intCast c, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hc
  push_cast at this
  exact this
end GlobalTheory.K5.Basic
