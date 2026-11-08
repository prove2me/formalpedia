-- Prove2me | solution 1 for HiddenPartition.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:49:22.978728+00:00
-- url     : https://prove2.me/submissions/260d645a-94fd-4f1b-b8a8-dd95bdb8225c

import Mathlib
import Definitions.Def_HiddenPartition_IsDomainPartition
import Definitions.Def_HiddenPartition_IsLocallyCoherent

set_option autoImplicit false

namespace Aux_HP34
open HiddenPartition

theorem mem_W {V A B : Type} [Fintype V] [DecidableEq B] {k : ℕ} (dom : V → Fin k)
    (f : V → A → B) (a : A) (v : V) : phi dom f a v ∈ W dom f a :=
  Finset.mem_image_of_mem _ (Finset.mem_univ v)

theorem uniq {V A B : Type} [Fintype V] [DecidableEq B] {k : ℕ} (dom : V → Fin k)
    (f : V → A → B) (hc : ∀ a a', a ≠ a' → (W dom f a ∩ W dom f a').card ≤ 1)
    (a a' : A) (x y : Fin k × B) (hxy : x ≠ y) (hx : x ∈ W dom f a) (hx' : x ∈ W dom f a')
    (hy : y ∈ W dom f a) (hy' : y ∈ W dom f a') : a = a' := by
  by_contra hne
  have h1 := hc a a' hne
  have hsub : ({x, y} : Finset (Fin k × B)) ⊆ W dom f a ∩ W dom f a' := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hx, hx'⟩
    · exact Finset.mem_inter.mpr ⟨hy, hy'⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hxy] at h2
  omega

end Aux_HP34

open HiddenPartition in
theorem solution {V A B : Type} [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k)
    (hdom : IsDomainPartition G dom) (hAB : Fintype.card A = Fintype.card B)
    (f : V → A → B) (t : ℕ) (ht : 2 ≤ t)
    (hf : IsLocallyCoherent t G dom f) (S : Fin k → V) (hS : ∀ i, dom (S i) = i) :
    Function.Bijective (fun p : A × Fin k => phi dom f p.1 (S p.2)) ∧
    ∀ a i i', (target G dom f).Adj (phi dom f a (S i)) (phi dom f a (S i')) ↔
      G.Adj (S i) (S i') := by
  have hc := hf.2.2.1 ht
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a, i⟩ ⟨a', i'⟩ h
    simp only [phi, Prod.mk.injEq, hS] at h
    obtain ⟨rfl, h2⟩ := h
    have := (hf.1 (S i)).1 h2
    rw [this]
  · rintro ⟨i, b⟩
    obtain ⟨a, ha⟩ := (hf.1 (S i)).2 b
    refine ⟨(a, i), ?_⟩
    simp only [phi, hS, ha]
  · intro a i i'
    have hinj := hf.2.1 a
    constructor
    · rintro ⟨hne, a', u', v', huv', hu', hv'⟩
      have : a' = a := Aux_HP34.uniq dom f hc a' a _ _ hne
        (hu' ▸ Aux_HP34.mem_W dom f a' u') (Aux_HP34.mem_W dom f a (S i))
        (hv' ▸ Aux_HP34.mem_W dom f a' v') (Aux_HP34.mem_W dom f a (S i'))
      subst this
      rw [← hinj hu', ← hinj hv']
      exact huv'
    · intro huv
      exact ⟨fun h => huv.ne (hinj h), a, S i, S i', huv, rfl, rfl⟩
