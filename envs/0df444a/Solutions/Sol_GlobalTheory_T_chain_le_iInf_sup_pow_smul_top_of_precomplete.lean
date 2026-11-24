-- Prove2me | solution 1 for GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:30.535713+00:00
-- url     : https://prove2.me/submissions/d1fd4918-2f20-49cc-8234-654327c172c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChainLeIInfSupPowSmulTopOfPrecomplete
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChainLeIInfSupPowSmulTopOfPrecompleteStatement
import Theorems.Thm_GlobalTheory_chain_le_iInf_sup_pow_smul_top


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
theorem _root_.solution : ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ) (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  first | exact @GlobalTheory.chain_le_iInf_sup_pow_smul_top | exact GlobalTheory.chain_le_iInf_sup_pow_smul_top | (intros; apply GlobalTheory.chain_le_iInf_sup_pow_smul_top <;> assumption)
end _root_.GlobalTheory.T
