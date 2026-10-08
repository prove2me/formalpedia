-- Prove2me | solution 1 for Menger27.Curves.no_extra_leg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:06:37.959445+00:00
-- url     : https://prove2.me/submissions/1c292066-8186-479b-bf5e-1b223e9f5685

import Mathlib
import Definitions.Def_Menger27_Curves_Basic



namespace Menger27.Curves

theorem nel_core {X : Type*} [MetricSpace X]
    (p : X) (n : ℕ) (horder : OrderAtMost p n) :
    ¬ HasNBein p (n + 1) := by
  rintro ⟨γ, hγ, hmeet⟩
  classical
  have hne : ∀ i : Fin (n+1), γ i 1 ≠ p := by
    intro i h
    have := (hγ i).1.2 (a₁ := 1) (a₂ := 0) (by rw [h, (hγ i).2])
    exact one_ne_zero (congrArg Subtype.val this)
  let S : Set X := Set.range (fun i : Fin (n+1) => γ i 1)
  have hSfin : S.Finite := Set.finite_range _
  obtain ⟨V, hVo, hpV, hVW, hcard⟩ := horder (Sᶜ) hSfin.isClosed.isOpen_compl
    (by intro h; obtain ⟨i, hi⟩ := h; exact hne i hi)
  have key : ∀ i : Fin (n+1), ∃ f ∈ frontier V, f ∈ Set.range (γ i) := by
    intro i
    have hc : IsPreconnected (Set.range (γ i)) :=
      isPreconnected_range (hγ i).1.1
    have h1 : (Set.range (γ i) ∩ V).Nonempty := ⟨p, ⟨0, (hγ i).2⟩, hpV⟩
    have h2 : (Set.range (γ i) \ V).Nonempty :=
      ⟨γ i 1, ⟨1, rfl⟩, fun h => hVW h ⟨i, rfl⟩⟩
    by_contra hno
    push_neg at hno
    have hsub : Set.range (γ i) ⊆ V ∪ (closure V)ᶜ := by
      intro x hx
      by_cases hxc : x ∈ closure V
      · left
        by_contra hxV
        exact hno x (by rw [frontier, hVo.interior_eq]; exact ⟨hxc, hxV⟩) hx
      · right; exact hxc
    obtain ⟨y, hy, hyV, hyc⟩ := hc V (closure V)ᶜ hVo isClosed_closure.isOpen_compl hsub h1
      (by
        obtain ⟨x, hx, hxV⟩ := h2
        refine ⟨x, hx, ?_⟩
        intro hxc
        exact hno x (by rw [frontier, hVo.interior_eq]; exact ⟨hxc, hxV⟩) hx)
    exact hyc (subset_closure hyV)
  choose f hf hfr using key
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hij'
    have : f i ∈ Set.range (γ i) ∩ Set.range (γ j) := ⟨hfr i, hij ▸ hfr j⟩
    rw [hmeet i j hij'] at this
    have hp : p ∉ frontier V := by
      rw [hVo.frontier_eq]; exact fun h => h.2 hpV
    exact hp (this ▸ hf i)
  have hsub : Set.range f ⊆ frontier V := by rintro _ ⟨i, rfl⟩; exact hf i
  have h5 : (Set.range f).encard = ENat.card (Fin (n+1)) := by
    rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]
  have h4 : (Set.range f).encard ≤ (frontier V).encard := Set.encard_le_encard hsub
  rw [h5] at h4
  have h3 : ((n+1 : ℕ) : ℕ∞) ≤ n := by
    have : ENat.card (Fin (n+1)) = ((n+1 : ℕ) : ℕ∞) := by simp
    exact this ▸ h4.trans hcard
  norm_cast at h3
  omega

end Menger27.Curves

open Menger27.Curves


theorem solution {X : Type*} [MetricSpace X]
    (p : X) (n : ℕ) (horder : OrderAtMost p n) :
    ¬ HasNBein p (n + 1) := by
  exact nel_core p n horder
