-- Prove2me | solution 1 for JardenShami.isHomogeneous_iff_color
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:28.922994+00:00
-- url     : https://prove2.me/submissions/1d471cb8-7e4d-493d-8e63-e1bb60992410

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Theorems.Thm_JardenShami_Pairs_exists_eq_mk

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
namespace JardenShami
theorem _root_.solution {A : Type*} [LinearOrder A] {D : Type*} (C : Coloring A D)
    (B : Set A) :
    IsHomogeneous C B ↔ ∀ (a b c d : A) (hab : a < b) (hcd : c < d),
      a ∈ B → b ∈ B → c ∈ B → d ∈ B → C.color a b hab = C.color c d hcd := by
  constructor
  · intro h a b c d hab hcd ha hb hc hd
    apply h
    · intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> assumption
    · intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> assumption
  · intro h p q hp hq
    obtain ⟨a, b, hab, rfl⟩ := p.exists_eq_mk
    obtain ⟨c, d, hcd, rfl⟩ := q.exists_eq_mk
    exact h a b c d hab hcd (hp a (Sym2.mem_mk_left a b)) (hp b (Sym2.mem_mk_right a b))
      (hq c (Sym2.mem_mk_left c d)) (hq d (Sym2.mem_mk_right c d))
end JardenShami
