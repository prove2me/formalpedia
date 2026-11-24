-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:08:00.571071+00:00
-- url     : https://prove2.me/submissions/29887a2f-7be9-477c-a3cf-4d0aa4221758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_sum_left_right_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_product_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_fixed_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_fixed_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeProduct
namespace GlobalTheory.CompanionTheory.HeckeProduct
theorem _root_.solution : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  intro G₁ G₂ V _ _ _ _ ρ K₁ K₂ f₁ f₁' f₁'' f₂ f₂' f₂'' h1 h2 hA hB v hv
  obtain ⟨a, ai⟩ := h1 f₁ (by simp)
  obtain ⟨a', ai'⟩ := h1 f₁' (by simp)
  obtain ⟨a'', ai''⟩ := h1 f₁'' (by simp)
  obtain ⟨b, bi⟩ := h2 f₂ (by simp)
  obtain ⟨b', bi'⟩ := h2 f₂' (by simp)
  obtain ⟨b'', bi''⟩ := h2 f₂'' (by simp)
  have hA' : ∀ w : V, (∀ k ∈ K₁, left ρ k w = w) → heckeSum (left ρ) K₁ f₁'' w
      = heckeSum (left ρ) K₁ f₁ (heckeSum (left ρ) K₁ f₁' w) := hA
  have hB' : ∀ w : V, (∀ k ∈ K₂, right ρ k w = w) → heckeSum (right ρ) K₂ f₂'' w
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' w) := hB
  have hv₂ : ∀ k ∈ K₂, right ρ k v = v := fun k hk =>
    hv (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  have hy := fixed_right ρ K₁ K₂ b' (fun k hk g => (bi' k hk g).1) (fun k hk g => (bi' k hk g).2) v hv
  have hx := fixed_right ρ K₁ K₂ b (fun k hk g => (bi k hk g).1) (fun k hk g => (bi k hk g).2) _ hy
  have hw := fixed_left ρ K₁ K₂ a' (fun k hk g => (ai' k hk g).1) (fun k hk g => (ai' k hk g).2) _ hy
  have hx₁ : ∀ k ∈ K₁, left ρ k (heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v))
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v) := fun k hk =>
    hx (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  rw [product_sum ρ K₁ K₂ a'' b'' (fun k hk g => (ai'' k hk g).2) (fun k hk g => (bi'' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a' b' (fun k hk g => (ai' k hk g).2) (fun k hk g => (bi' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a b (fun k hk g => (ai k hk g).2) (fun k hk g => (bi k hk g).2) _ hw,
    hB' v hv₂, hA' _ hx₁, sum_left_right_comm ρ K₁ K₂ a' b]
end GlobalTheory.CompanionTheory.HeckeProduct
