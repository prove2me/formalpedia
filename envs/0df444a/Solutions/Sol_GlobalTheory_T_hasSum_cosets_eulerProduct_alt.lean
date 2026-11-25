-- Prove2me | solution 1 for GlobalTheory.T.hasSum_cosets_eulerProduct_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:19.128521+00:00
-- url     : https://prove2.me/submissions/afddc51a-2e5f-4fd7-8f7c-254dd5ab1e23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProductStatement
import Theorems.Thm_GlobalTheory_CosetEuler_hasSum_cosets_eulerProduct


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
theorem _root_.solution : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  first | exact @GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | exact GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | (intros; apply GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct <;> assumption)
end _root_.GlobalTheory.T
