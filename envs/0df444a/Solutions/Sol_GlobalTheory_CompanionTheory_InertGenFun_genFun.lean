-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertGenFun.genFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:11:37.032126+00:00
-- url     : https://prove2.me/submissions/1745d31d-059b-43e5-b826-f0bcb04bfd27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_GeneratingFunctionIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_InertGenFun_hasSum_counts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertGenFun_hasSum_of_counts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertGenFun
namespace GlobalTheory.CompanionTheory.InertGenFun
theorem _root_.solution : GenFun := by
  intro ι f l c q N X hc hq hf hcount hX
  have hA : ∀ j, c * q ^ (2 * N * (j / 2) + j) ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hcg : ∀ j, Nat.card {i // f i - l ≤ j} = c * q ^ (2 * N * (j / 2) + j) := by
    intro j
    rw [← hcount j]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by have := hf i; omega))
  have h := hasSum_of_counts (fun i => f i - l) (fun j => c * q ^ (2 * N * (j / 2) + j)) hA hcg X _
    (hasSum_counts q N c X hX)
  have key : (fun i => X ^ f i) = fun i => X ^ l * X ^ (f i - l) := by
    funext i
    rw [← pow_add]
    congr 1
    have := hf i
    omega
  rw [key, show (c : ℂ) * X ^ l * jFac q N X =
    X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
  exact h.mul_left _
end GlobalTheory.CompanionTheory.InertGenFun
