-- Prove2me | solution 1 for HiddenPartition.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:07:53.74665+00:00
-- url     : https://prove2.me/submissions/ec856a1b-fc78-4305-bdda-61078def61b9

import Mathlib
import Definitions.Def_HiddenPartition_IsDomainPartition
import Definitions.Def_HiddenPartition_IsLocallyCoherent

set_option autoImplicit false

namespace Aux_HP33
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

end Aux_HP33

open HiddenPartition in
theorem solution {V A B : Type} [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k)
    (hdom : IsDomainPartition G dom) (hAB : Fintype.card A = Fintype.card B)
    (f : V → A → B) (t : ℕ) (ht : 2 ≤ t)
    (hf : IsLocallyCoherent t G dom f) :
    (∀ x y, (target G dom f).Adj x y → ∃! a, Generates G dom f a s(x, y)) ∧
    (∀ a, ∃ e : G ≃g (target G dom f).induce (W dom f a : Set (Fin k × B)),
      ∀ v, (e v : Fin k × B) = phi dom f a v) := by
  have hc := hf.2.2.1 ht
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨hne, a, u, v, huv, hu, hv⟩ := hxy
    refine ⟨a, ⟨u, v, huv, by rw [hu, hv]⟩, ?_⟩
    rintro a' ⟨u', v', _, he⟩
    have hxa : x ∈ W dom f a := hu ▸ Aux_HP33.mem_W dom f a u
    have hya : y ∈ W dom f a := hv ▸ Aux_HP33.mem_W dom f a v
    rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Aux_HP33.uniq dom f hc a' a x y hne (h1 ▸ Aux_HP33.mem_W dom f a' u') hxa
        (h2 ▸ Aux_HP33.mem_W dom f a' v') hya
    · exact Aux_HP33.uniq dom f hc a' a x y hne (h1 ▸ Aux_HP33.mem_W dom f a' v') hxa
        (h2 ▸ Aux_HP33.mem_W dom f a' u') hya
  · intro a
    have hinj := hf.2.1 a
    let e : V ≃ (W dom f a : Set (Fin k × B)) :=
      Equiv.ofBijective (fun v => ⟨phi dom f a v, Aux_HP33.mem_W dom f a v⟩)
        ⟨fun u v h => hinj (congrArg Subtype.val h), by
          rintro ⟨x, hx⟩
          obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
          exact ⟨v, Subtype.ext hv⟩⟩
    refine ⟨⟨e, ?_⟩, fun v => rfl⟩
    intro u v
    show (target G dom f).Adj (phi dom f a u) (phi dom f a v) ↔ G.Adj u v
    constructor
    · rintro ⟨hne, a', u', v', huv', hu', hv'⟩
      have : a' = a := Aux_HP33.uniq dom f hc a' a _ _ hne
        (hu' ▸ Aux_HP33.mem_W dom f a' u') (Aux_HP33.mem_W dom f a u)
        (hv' ▸ Aux_HP33.mem_W dom f a' v') (Aux_HP33.mem_W dom f a v)
      subst this
      rw [← hinj hu', ← hinj hv']
      exact huv'
    · intro huv
      exact ⟨fun h => huv.ne (hinj h), a, u, v, huv, rfl, rfl⟩
