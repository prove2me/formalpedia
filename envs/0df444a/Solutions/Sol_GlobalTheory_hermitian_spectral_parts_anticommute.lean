-- Prove2me | solution 1 for GlobalTheory.hermitian_spectral_parts_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:19.528491+00:00
-- url     : https://prove2.me/submissions/f07472d1-1c9c-42b9-ae94-a367800cc366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommute
import Theorems.Thm_GlobalTheory_spectral_parts_of_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian →
      J * Y = -(Y * J) →
      ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  intro n _ _ Y J hY hJ
  refine spectral_parts_of_diag Y J (hY.eigenvectorUnitary : Matrix n n ℂ) hY.eigenvalues
    ?_ ?_ ?_ hJ
  · exact hY.eigenvectorUnitary.2.1
  · exact hY.eigenvectorUnitary.2.2
  · exact hY.spectral_theorem
end GlobalTheory
