-- Prove2me | solution 1 for GlobalTheory.T.linear_map_zero_of_injective_full_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:17:09.828923+00:00
-- url     : https://prove2.me/submissions/dd45dfee-694c-40e8-abba-20a652a937b0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRank
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRankStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Perf_map_eq_zero_of_comp_injective_of_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N] [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ) (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N), Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq | exact GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq <;> assumption)
end _root_.GlobalTheory.T
