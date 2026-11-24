-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.An.one_le_norm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:26.749034+00:00
-- url     : https://prove2.me/submissions/4e60bb78-f8c1-4e86-83ac-26215d077b0b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__LogDerOne_a1ce1da79bfc3842
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_OneLeNormOneSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.An
open GlobalTheory.Mem.An
namespace GlobalTheory.CompanionTheory.An
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h1 : χ ≠ 1) {w : ℂ}
    (hw : LFunction χ w = 0) (hB : w ∉ zerosIn χ 0 1) : 1 ≤ ‖1 - w‖ := by
  have hre : w.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (not_lt.1 h) hw
  by_cases h0 : 0 < w.re
  · have him : 1 < |w.im| := by
      by_contra h
      refine hB ⟨h0, hre, ?_, hw⟩
      simpa using not_lt.1 h
    have := Complex.abs_im_le_norm (1 - w)
    have e : |(1 - w).im| = |w.im| := by simp
    linarith
  · have := Complex.abs_re_le_norm (1 - w)
    have e : (1 - w).re = 1 - w.re := by simp
    rw [e] at this
    have := le_abs_self (1 - w.re)
    linarith [not_lt.1 h0]
end GlobalTheory.CompanionTheory.An
