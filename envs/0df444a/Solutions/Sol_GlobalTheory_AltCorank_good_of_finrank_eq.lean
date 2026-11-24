-- Prove2me | solution 1 for GlobalTheory.AltCorank.good_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:34.711804+00:00
-- url     : https://prove2.me/submissions/4c11b512-a5fb-4bff-a9e0-51ba6e6be213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
import Theorems.Thm_GlobalTheory_AltCorank_good_step
import Theorems.Thm_GlobalTheory_AltCorank_finrank_inf_ker
import Theorems.Thm_GlobalTheory_AltCorank_exists_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.AltCorank
theorem _root_.solution [Module.Finite K V] (n : ℕ) :
    ∀ S₁ S₂ : Submodule K V, finrank K S₁ = n → finrank K S₂ = n → Good S₁ S₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S₁ S₂ h₁ h₂
  by_cases hE : S₁ = S₂
  · subst hE
    by_cases hx : ∃ x : Fin 2 → V, (∀ a, x a ∈ S₁) ∧ LinearIndependent K x
    · obtain ⟨x, hx, hli⟩ := hx
      have n0 : x 0 ∉ Submodule.span K {x 1} := by
        have := hli.notMem_span_image (s := {1}) (x := 0) (by simp)
        simpa using this
      have n1 : x 1 ∉ Submodule.span K {x 0} := by
        have := hli.notMem_span_image (s := {0}) (x := 1) (by simp)
        simpa using this
      obtain ⟨φ, a1, a2⟩ := exists_dual _ _ n0
      obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ n1
      have a3 := a2 _ (Submodule.mem_span_singleton_self _)
      have b3 := b2 _ (Submodule.mem_span_singleton_self _)
      have hlt : finrank K (S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule K V) < n := by
        have := finrank_inf_ker S₁ φ _ (hx 0) a1
        have := Submodule.finrank_mono
          (inf_le_left : S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ ≤ S₁ ⊓ LinearMap.ker φ)
        omega
      refine good_step S₁ S₁ _ _ (x 0) (x 1) φ ψ a1 a3 b3 b1 (hx 1) (Or.inl (hx 0)) ?_ ?_
        (ih _ hlt _ _ rfl rfl)
      · intro y h1 h2 h3
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro y ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    · exact ⟨0, fun _ => rfl, fun x h1 _ h2 => hx ⟨x, h1, h2⟩⟩
  · have l1 : ¬ S₁ ≤ S₂ := fun h => hE (Submodule.eq_of_le_of_finrank_eq h (h₁.trans h₂.symm))
    have l2 : ¬ S₂ ≤ S₁ := fun h =>
      hE (Submodule.eq_of_le_of_finrank_eq h (h₂.trans h₁.symm)).symm
    obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.1 l1
    obtain ⟨v, hv2, hv1⟩ := SetLike.not_le_iff_exists.1 l2
    obtain ⟨φ, a1, a2⟩ := exists_dual _ _ hu2
    obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ hv1
    have c1 := finrank_inf_ker S₁ φ u hu1 a1
    have c2 := finrank_inf_ker S₂ ψ v hv2 b1
    refine good_step S₁ S₂ (S₁ ⊓ LinearMap.ker φ) (S₂ ⊓ LinearMap.ker ψ) u v φ ψ a1 (a2 _ hv2)
      (b2 _ hu1) b1 hv2 (Or.inr b2) ?_ ?_ (ih (n - 1) (by omega) _ _ (by omega) (by omega))
    · intro y h1 h2 _
      exact ⟨h1, h2⟩
    · rintro y ⟨h1, h2⟩
      exact ⟨h1, a2 _ h1, h2⟩
end GlobalTheory.AltCorank
