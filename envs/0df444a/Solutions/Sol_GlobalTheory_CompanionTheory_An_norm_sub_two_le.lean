-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.An.norm_sub_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:25.82944+00:00
-- url     : https://prove2.me/submissions/8eaebbce-6cda-4f2f-bca4-8ec66ea58900

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
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {w : ℂ}
    (hw : w ∈ zerosIn χ 0 1) : ‖w - 2‖ ≤ 7 / 2 := by
  obtain ⟨h0, h1, h2, -⟩ := hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a : (w - 2).re = w.re - 2 := by simp
  have b : (w - 2).im = w.im := by simp
  rw [a, b]
  have h3 : |w.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h4 : |w.im| ≤ 1 := by simpa using h2
  linarith
end GlobalTheory.CompanionTheory.An
