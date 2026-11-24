-- Prove2me | solution 1 for GlobalTheory.exists_hyperbolic_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:37.164615+00:00
-- url     : https://prove2.me/submissions/4a41c5ff-4e53-475e-8a0e-21415042211a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsHyperbolicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open Module
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → h.Nondegenerate → ∀ (W : Submodule E V), (∀ x ∈ W, (∀ y ∈ W, h x y = 0) → x = 0) → ∀ (i : ℕ) (e : Fin i → V), LinearIndependent E e → (∀ a b, h (e a) (e b) = 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0) → Module.finrank E W + 2 * i = Module.finrank E V → ∃ f : Fin i → V, (∀ a b, h (f a) (f b) = 0) ∧ (∀ a b, h (f a) (e b) = if a = b then 1 else 0) ∧ (∀ a, ∀ x ∈ W, h x (f a) = 0) ∧ W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ := by
  intro E V _ _ _ _ _ _ h hs hn W hW i e he hee heW hdim
  set m := finrank E W with hm
  let b := Module.finBasis E W
  let w : Fin m → V := fun j => (b j : V)
  have hwW : ∀ j, w j ∈ W := fun j => (b j).2
  let u : Fin i ⊕ Fin m → V := Sum.elim e w
  have hw : LinearIndependent E w := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hu : LinearIndependent E u := by
    refine he.sum_type hw ?_
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hxW : x ∈ W := (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwW j)) hx2
    refine hW x hxW fun y hy => ?_
    have hle : Submodule.span E (Set.range e) ≤ LinearMap.ker (h y) :=
      Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact heW a y hy)
    rw [← hs.eq, show h y x = 0 from hle hx1, map_zero]
  let L : V →ₗ[E] (Fin i ⊕ Fin m → E) := LinearMap.pi fun k => h (u k)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨μ, hμ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hz : ∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k = 0 := by
      refine hn.1 _ fun y => ?_
      have h0 : μ (L y) = 0 := hle (LinearMap.mem_range_self L y)
      rw [LinearMap.pi_apply_eq_sum_univ] at h0
      have h1 : h (∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k) y = ∑ k, L y k • μ fun j => if k = j then (1 : E) else 0 := by
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, L, LinearMap.pi_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1, h0]
    have hc0 : ∀ k, μ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
      have := Fintype.linearIndependent_iff.mp hu _ hz k
      simpa using this
    apply hμ
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [hc0, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]
  choose g hg using fun a : Fin i => hL fun k => if k = Sum.inl a then (1 : E) else 0
  have hge : ∀ a b, h (e b) (g a) = if b = a then 1 else 0 := fun a b => by
    have := congrFun (hg a) (Sum.inl b)
    simpa [L, u] using this
  have hgw : ∀ a j, h (w j) (g a) = 0 := fun a j => by
    have := congrFun (hg a) (Sum.inr j)
    simpa [L, u] using this
  have hgW : ∀ a, ∀ x ∈ W, h x (g a) = 0 := by
    intro a x hx
    have hx' : x = ∑ j, b.repr ⟨x, hx⟩ j • w j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    simp [map_sum, hgw]
  set f : Fin i → V := fun a => g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c with hf
  have hfa : ∀ a, f a = g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c := fun a => rfl
  have hfe : ∀ a b, h (e b) (f a) = if b = a then 1 else 0 := by
    intro a b
    rw [hfa]
    simp [map_sub, map_sum, hee, hge]
  have hfe' : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs.eq, hfe]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hfW : ∀ a, ∀ x ∈ W, h x (f a) = 0 := by
    intro a x hx
    rw [hfa]
    simp [map_sub, map_sum, hgW a x hx, heW _ x hx]
  have hff : ∀ a b, h (f a) (f b) = 0 := by
    intro a b
    have hs' : starRingEnd E (h (g b) (g a)) = h (g a) (g b) := hs.eq (g b) (g a)
    have h1 : h (f a) (f b) = h (f a) (g b) - 2⁻¹ * h (g a) (g b) := by
      conv_lhs => rw [hfa b]
      simp [map_sub, map_sum, hfe']
    rw [h1, hfa a]
    simp [map_sub, map_sum, hge, hs', map_ofNat]
    ring
  let v : Fin i ⊕ (Fin i ⊕ Fin m) → V := Sum.elim f u
  have hu0 : ∀ c k, h (e c) (u k) = 0 := by
    intro c k
    rcases k with d | j
    · exact hee c d
    · show h (e c) (w j) = 0
      rw [← hs.eq, heW c _ (hwW j)]
      simp
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro γ hγ
    simp only [v] at hγ
    rw [Fintype.sum_sum_type] at hγ
    simp only [Sum.elim_inl, Sum.elim_inr] at hγ
    have hfst : ∀ a, γ (Sum.inl a) = 0 := by
      intro a
      have := congrArg (h (e a)) hγ
      simpa [map_add, map_sum, hfe, hu0] using this
    have hrest : ∑ k, γ (Sum.inr k) • u k = 0 := by simpa [hfst] using hγ
    intro k
    rcases k with a | k
    · exact hfst a
    · exact Fintype.linearIndependent_iff.mp hu _ hrest k
  have hspan : Submodule.span E (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp; omega)
  refine ⟨f, hff, hfe', hfW, ?_⟩
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rcases k with a | c | j
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨c, rfl⟩))
  · exact Submodule.mem_sup_left (hwW j)
end _root_.GlobalTheory
end GlobalTheory
