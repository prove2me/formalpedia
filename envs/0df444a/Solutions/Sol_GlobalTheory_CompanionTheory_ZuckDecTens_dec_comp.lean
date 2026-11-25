-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckDecTens.dec_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:34:59.548274+00:00
-- url     : https://prove2.me/submissions/861d0197-a72e-4f3f-8721-434ede34e910

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTensorFromHomLaws

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecTens
universe u
variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
namespace GlobalTheory.CompanionTheory.ZuckDecTens
theorem _root_.solution {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop} (hc : IsLinCat N Hom) {A B P : Type} [Fintype A] [Fintype B]
    [Fintype P] (e : P ≃ A × B) {X : O} {Z : A → O} {S : A → B → O}
    {j : ∀ a, N (Z a) →ₗ[ℂ] N X} {q : ∀ a, N X →ₗ[ℂ] N (Z a)} (h : IsDec Hom X Z j q)
    {io : ∀ a b, N (S a b) →ₗ[ℂ] N (Z a)} {pr : ∀ a b, N (Z a) →ₗ[ℂ] N (S a b)}
    (h2 : ∀ a, IsDec Hom (Z a) (S a) (io a) (pr a)) :
    IsDec Hom X (fun p => S (e p).1 (e p).2) (fun p => j (e p).1 ∘ₗ io (e p).1 (e p).2)
      (fun p => pr (e p).1 (e p).2 ∘ₗ q (e p).1) where
  io_hom p := hc.comp _ _ _ _ _ ((h2 _).io_hom _) (h.io_hom _)
  pr_hom p := hc.comp _ _ _ _ _ (h.pr_hom _) ((h2 _).pr_hom _)
  sum := by
    rw [Equiv.sum_comp e (fun p : A × B => (j p.1 ∘ₗ io p.1 p.2) ∘ₗ (pr p.1 p.2 ∘ₗ q p.1)),
      Fintype.sum_prod_type, ← h.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ext x
    have := congrArg (fun f => j a (f (q a x))) (h2 a).sum
    simpa [map_sum] using this
  pr_io p := by
    ext x
    have h1 := LinearMap.congr_fun (h.pr_io (e p).1) (io (e p).1 (e p).2 x)
    have h3 := LinearMap.congr_fun ((h2 (e p).1).pr_io (e p).2) x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h3 ⊢
    rw [h1, h3]
  pr_io_ne p p' hne := by
    have hne' : e p ≠ e p' := fun hh => hne (e.injective hh)
    generalize e p = s at hne'
    generalize e p' = s' at hne'
    obtain ⟨a, b⟩ := s
    obtain ⟨a', b'⟩ := s'
    ext x
    by_cases ha : a = a'
    · subst ha
      have hb : b ≠ b' := fun hh => hne' (by rw [hh])
      have h1 := LinearMap.congr_fun (h.pr_io a) (io a b' x)
      have h3 := LinearMap.congr_fun ((h2 a).pr_io_ne b b' hb) x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h3 ⊢
      rw [h1, h3]
    · have h1 := LinearMap.congr_fun (h.pr_io_ne a a' ha) (io a' b' x)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 ⊢
      rw [h1, map_zero]
end GlobalTheory.CompanionTheory.ZuckDecTens
