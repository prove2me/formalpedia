-- Prove2me | solution 1 for GlobalTheory.NormDetIndex.norm_eq_of_associated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:48.455504+00:00
-- url     : https://prove2.me/submissions/125aeec7-ffd8-4e8f-8eb8-951f6ebeefb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormDetIndex
open Module Submodule
namespace GlobalTheory.NormDetIndex
theorem _root_.solution (l : ℕ) [Fact (Nat.Prime l)] {x y : ℤ_[l]} (h : Associated x y) :
    ‖x‖ = ‖y‖ := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]
end GlobalTheory.NormDetIndex
