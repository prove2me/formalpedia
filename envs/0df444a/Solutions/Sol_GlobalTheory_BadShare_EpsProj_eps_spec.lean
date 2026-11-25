-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.eps_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:41.885637+00:00
-- url     : https://prove2.me/submissions/b7e3440b-5067-4402-ac65-69f7d4810b98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_isProj_eps
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_mem_range_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.EpsProj
variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}
namespace GlobalTheory.BadShare.EpsProj
theorem _root_.solution : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  intro G _ _ M _ _ _ ρ S χ h1 hm c1 cm
  refine ⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩
  · simp only [eps, if_pos h1, c1, inv_one, one_div]
  · intro n x hx h
    have hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ)) :=
      fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)
    have hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ)))) :=
      LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx
    simpa [rk] using hli.fintype_card_le_finrank
end GlobalTheory.BadShare.EpsProj
