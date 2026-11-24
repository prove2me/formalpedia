-- Prove2me | solution 1 for GlobalTheory.T.exists_maximal_abelian_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:08:08.783771+00:00
-- url     : https://prove2.me/submissions/43ed1cb4-69ee-4145-86c7-54ef5b982fdd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsMaximalAbelianHermitian
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsMaximalAbelianHermitianStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermitianCommuting_exists_maximal_commuting_hermitian_subspace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧ (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧ ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | exact GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | (intros; apply GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace <;> assumption)
end _root_.GlobalTheory.T
