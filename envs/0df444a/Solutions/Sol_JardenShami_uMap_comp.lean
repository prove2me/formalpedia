-- Prove2me | solution 1 for JardenShami.uMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:48.864184+00:00
-- url     : https://prove2.me/submissions/751bddce-6f4d-486a-9639-71e1b9a55c2f

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Theorems.Thm_JardenShami_uMap_color

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {A : Type w} [LinearOrder A] {D : Type v}
namespace JardenShami
theorem _root_.solution {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    ∀ t : Dset C c, ∃ h : uMap C b c hbc t ∈ Dset C b,
      uMap C a b hab ⟨uMap C b c hbc t, h⟩ = uMap C a c (hab.trans hbc) t := by
  intro t
  -- `u_{b,c}(t) = C(b,d)` for the chosen witness `d > c` of `t ∈ D_c`.
  have hbd : b < Classical.choose t.2 := hbc.trans (Classical.choose_spec t.2).fst
  exact ⟨⟨Classical.choose t.2, hbd, rfl⟩, uMap_color hC hab hbd⟩
end JardenShami
