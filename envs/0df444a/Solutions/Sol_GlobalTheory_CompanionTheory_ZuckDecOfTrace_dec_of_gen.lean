-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckDecOfTrace.dec_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:37:05.643025+00:00
-- url     : https://prove2.me/submissions/75809cfb-d29f-42f2-953b-b0d289082df0

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTrace

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecOfTrace
universe u
variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}
namespace GlobalTheory.CompanionTheory.ZuckDecOfTrace
theorem _root_.solution (hc : IsLinCat N Hom) {P : Type} {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X Z : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr)
    {j : N Z →ₗ[ℂ] N X} {q : N X →ₗ[ℂ] N Z} (hj : Hom Z X j) (hq : Hom X Z q) (hqj : q ∘ₗ j = LinearMap.id)
    {I : Type} [Fintype I] {e : I → P} (he : Function.Injective e)
    (g : ∀ i, homSub hc (T (e i)) Z) (hg0 : ∀ i, g i ≠ 0) (hg : ∀ i w, ∃ c : ℂ, c • g i = w)
    (h0 : ∀ ν, (∀ i, e i ≠ ν) → ∀ w : homSub hc (T ν) Z, w = 0) :
    ∃ io pr, IsDec Hom Z (fun i => T (e i)) io pr := by
  classical
  let S : (N Z →ₗ[ℂ] N Z) → Prop := fun f =>
    ∃ r : ∀ i, homSub hc Z (T (e i)), ∑ i, (g i).1 ∘ₗ (r i).1 = f
  have S0 : S 0 := ⟨0, by simp⟩
  have Sadd : ∀ f f', S f → S f' → S (f + f') := by
    rintro _ _ ⟨r, rfl⟩ ⟨r', rfl⟩
    exact ⟨r + r', by simp [LinearMap.comp_add, Finset.sum_add_distrib]⟩
  have Sterm : ∀ ν (f : N (T ν) →ₗ[ℂ] N Z) (h : N Z →ₗ[ℂ] N (T ν)), Hom _ _ f → Hom _ _ h → S (f ∘ₗ h) := by
    intro ν f h hf hh
    by_cases hν : ∃ i, e i = ν
    · obtain ⟨i, rfl⟩ := hν
      obtain ⟨c, hc'⟩ := hg i ⟨f, hf⟩
      have hc'' : c • (g i).1 = f := congrArg Subtype.val hc'
      refine ⟨Pi.single i (c • ⟨h, hh⟩), ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [← hc'', LinearMap.comp_smul, LinearMap.smul_comp]
      · intro i' _ hi'
        simp [Pi.single_eq_of_ne hi']
      · simp
    · push Not at hν
      have : f = 0 := congrArg Subtype.val (h0 ν hν ⟨f, hf⟩)
      rw [this, LinearMap.zero_comp]
      exact S0
  have Sid : S LinearMap.id := by
    have : (LinearMap.id : N Z →ₗ[ℂ] N Z) = ∑ k, (q ∘ₗ io k) ∘ₗ (pr k ∘ₗ j) := by
      ext x
      have e1 := LinearMap.congr_fun hd.sum (j x)
      have e2 : q (j x) = x := LinearMap.congr_fun hqj x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e1 ⊢
      rw [← map_sum, e1, e2]
    rw [this]
    exact Finset.sum_induction _ S Sadd S0 fun k _ =>
      Sterm _ _ _ (hc.comp _ _ _ _ _ (hd.io_hom k) hq) (hc.comp _ _ _ _ _ hj (hd.pr_hom k))
  obtain ⟨r, hr⟩ := Sid
  have hne : ∀ i i', i ≠ i' → (r i).1 ∘ₗ (g i').1 = 0 := fun i i' h =>
    hT.2.2 (e i') (e i) (fun h' => h (he h').symm) _ (hc.comp _ _ _ _ _ (g i').2 (r i).2)
  refine ⟨fun i => (g i).1, fun i => (r i).1, fun i => (g i).2, fun i => (r i).2, hr, fun i => ?_, hne⟩
  obtain ⟨c, hc'⟩ := hT.2.1 (e i) _ (hc.comp _ _ _ _ _ (g i).2 (r i).2)
  have h1 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = (g i).1 := by rw [hr, LinearMap.id_comp]
  have h2 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = c • (g i).1 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Finset.sum_eq_single i]
    · have : (r i).1 ((g i).1 x) = c • x := LinearMap.congr_fun hc' x
      rw [this, map_smul]; rfl
    · intro i' _ hi'
      have : (r i').1 ((g i).1 x) = 0 := LinearMap.congr_fun (hne i' i hi') x
      rw [this, map_zero]
    · simp
  have h3 : (c - 1) • (g i).1 = 0 := by rw [sub_smul, one_smul, ← h2, h1, sub_self]
  have h4 : (g i).1 ≠ 0 := fun h => hg0 i (Subtype.ext h)
  have h5 : c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h4)
  rw [hc', h5, one_smul]
end GlobalTheory.CompanionTheory.ZuckDecOfTrace
