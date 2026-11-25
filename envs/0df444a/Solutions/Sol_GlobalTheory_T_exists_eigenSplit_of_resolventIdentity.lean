-- Prove2me | solution 1 for GlobalTheory.T.exists_eigenSplit_of_resolventIdentity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:47:22.862114+00:00
-- url     : https://prove2.me/submissions/d0514420-eb5e-42b2-bf13-229d1c76313f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEigenSplitOfResolventIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEigenSplitOfResolventIdentityStatement
import Theorems.Thm_GlobalTheory_exists_sum_eigen_split_of_resolvent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  first | exact @GlobalTheory.exists_sum_eigen_split_of_resolvent | exact GlobalTheory.exists_sum_eigen_split_of_resolvent | (intros; apply GlobalTheory.exists_sum_eigen_split_of_resolvent <;> assumption)
end _root_.GlobalTheory.T
