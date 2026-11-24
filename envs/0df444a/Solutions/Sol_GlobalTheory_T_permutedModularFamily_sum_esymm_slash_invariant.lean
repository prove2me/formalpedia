-- Prove2me | solution 1 for GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:49.35906+00:00
-- url     : https://prove2.me/submissions/93c1f070-7aa0-4e39-8740-792cedd654bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariantStatement
import Theorems.Thm_GlobalTheory_QFam_sum_esymm_slash


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), ActBij act → IsFam act w f → ∀ γ : SL(2, ℤ), ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧ ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ = fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  first | exact @GlobalTheory.QFam.sum_esymm_slash | exact GlobalTheory.QFam.sum_esymm_slash | (intros; apply GlobalTheory.QFam.sum_esymm_slash <;> assumption)
end _root_.GlobalTheory.T
