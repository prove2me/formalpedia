-- Prove2me | solution 1 for JardenShami.uMap_color
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:01.858485+00:00
-- url     : https://prove2.me/submissions/c726f317-3e0b-4cec-877b-6d343a492e58

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {A : Type w} [LinearOrder A] {D : Type v}
namespace JardenShami
theorem _root_.solution {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    uMap C a b hab ⟨C.color b c hbc, c, hbc, rfl⟩ = C.color a c (hab.trans hbc) := by
  -- Any two witnesses `c, c' > b` with the same color `C(b,·)` give the same `C(a,·)`.
  have key : ∀ (c' : A) (hbc' : b < c'), C.color b c' hbc' = C.color b c hbc →
      C.color a c' (hab.trans hbc') = C.color a c (hab.trans hbc) := by
    intro c' hbc' h
    rcases lt_trichotomy c c' with hcc | rfl | hcc
    · exact (hC a b c c' hab hbc hcc h.symm).symm
    · rfl
    · exact hC a b c' c hab hbc' hcc h
  exact key _ _ (Classical.choose_spec (⟨C.color b c hbc, c, hbc, rfl⟩ : Dset C b).2).2
end JardenShami
