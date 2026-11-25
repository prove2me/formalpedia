-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_padicInt_domain_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:41.697774+00:00
-- url     : https://prove2.me/submissions/b38a81ab-b751-4233-97f8-e00be09b9d0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbeddingStatement
import Theorems.Thm_GlobalTheory_CompletionEmbed_exists_finite_padicInt_domain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  first | exact @GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | exact GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | (intros; apply GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain <;> assumption)
end _root_.GlobalTheory.T
