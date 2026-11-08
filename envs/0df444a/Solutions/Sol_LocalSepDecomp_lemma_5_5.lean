-- Prove2me | solution 1 for LocalSepDecomp.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:54:02.862724+00:00
-- url     : https://prove2.me/submissions/a478068b-fad5-4867-8b6e-9b5656a60c63

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

universe u

namespace Aux_LSD55

open SimpleGraph LocalSepDecomp

theorem simR_eq {V : Type*} (G : SimpleGraph V) (r : ℕ) (hr : r ≤ 2) (X : Set V)
    (a b : Sym2 V) (h : simR G r X a b) : a = b := by
  obtain ⟨ha, _, hab | ⟨u, v, W, ⟨⟨hu, hv, _⟩, hcyc | hlen⟩, hhead, _⟩⟩ := h
  · exact hab
  · exfalso
    obtain ⟨w, c, ⟨hc, hcl⟩, _⟩ := hcyc
    have := hc.three_le_length
    omega
  · exfalso
    cases W with
    | nil => simp at hlen
    | @cons _ v' _ h W' =>
      have h0 : W'.length = 0 := by rw [Walk.length_cons] at hlen; omega
      have hv' := Walk.eq_of_length_eq_zero h0
      subst hv'
      cases W' with
      | nil =>
        simp at hhead
        obtain ⟨_, x, y, hxy, hx, hy⟩ := ha
        rw [← hhead] at hxy
        have : y ∈ s(u, v') := by rw [hxy]; exact Sym2.mem_mk_right x y
        rcases Sym2.mem_iff.mp this with rfl | rfl
        · exact hy hu
        · exact hy hv
      | cons _ _ => simp at h0

end Aux_LSD55

open SimpleGraph LocalSepDecomp in
theorem solution {V : Type u} (G : SimpleGraph V) (hG : G.Connected) (r : ℕ) (hr : r ≤ 2)
    (X : Set V) (hX : IsTightRLocalSeparator G r X) : X.encard = 1 := by
  obtain ⟨F₁, F₂, ⟨⟨e, he, rfl⟩, htight⟩, _, _⟩ := hX
  have key : ∀ f, Relation.TransGen (simR G r X) e f → f = e := by
    intro f hf
    induction hf with
    | single h => exact (Aux_LSD55.simR_eq G r hr X _ _ h).symm
    | tail _ h ih => rw [← Aux_LSD55.simR_eq G r hr X _ _ h]; exact ih
  obtain ⟨_, x, y, rfl, hx, hy⟩ := he
  rw [Set.encard_eq_one]
  refine ⟨x, ?_⟩
  ext z
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hz
    obtain ⟨f, hf, hzf⟩ := htight z hz
    have := key f hf
    rw [this] at hzf
    rcases Sym2.mem_iff.mp hzf with rfl | rfl
    · rfl
    · exact absurd hz hy
  · rintro rfl; exact hx
