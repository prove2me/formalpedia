-- Prove2me | solution 1 for GlobalTheory.T.hermitian_spectral_projections_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:08.102361+00:00
-- url     : https://prove2.me/submissions/79dca77f-22a5-4d56-a29d-78adebc52cd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommuteStatement
import Theorems.Thm_GlobalTheory_hermitian_spectral_parts_anticommute


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian → J * Y = -(Y * J) → ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧ (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧ N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧ J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  first | exact @GlobalTheory.hermitian_spectral_parts_anticommute | exact GlobalTheory.hermitian_spectral_parts_anticommute | (intros; apply GlobalTheory.hermitian_spectral_parts_anticommute <;> assumption)
end _root_.GlobalTheory.T
