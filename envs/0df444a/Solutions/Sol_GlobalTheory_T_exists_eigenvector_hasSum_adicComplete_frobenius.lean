-- Prove2me | solution 1 for GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:31.775261+00:00
-- url     : https://prove2.me/submissions/11f9b636-df18-4bea-a4b0-956f9236720a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorHasSumAdicCompleteFrobenius
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement
import Theorems.Thm_GlobalTheory_abssum_eigen_lim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  first | exact @GlobalTheory.abssum_eigen_lim | exact GlobalTheory.abssum_eigen_lim | (intros; apply GlobalTheory.abssum_eigen_lim <;> assumption)
end _root_.GlobalTheory.T
