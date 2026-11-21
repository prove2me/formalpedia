-- Prove2me | solution 1 for JardenShami.uMap_wellDefined_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:47.053184+00:00
-- url     : https://prove2.me/submissions/7c50dcf5-334c-4b3c-bd3c-61bf42398b02

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
theorem _root_.solution (C : Coloring A D) :
    (∀ (a b c c' : A) (hab : a < b) (hbc : b < c) (hbc' : b < c'),
        C.color b c hbc = C.color b c' hbc' →
          C.color a c (hab.trans hbc) = C.color a c' (hab.trans hbc')) ↔
      IsLocallyAdditive C := by
  constructor
  · intro hwd a b c d hab hbc hcd h
    exact hwd a b c d hab hbc (hbc.trans hcd) h
  · intro hC a b c c' hab hbc hbc' h
    rcases lt_trichotomy c c' with hcc | rfl | hcc
    · exact hC a b c c' hab hbc hcc h
    · rfl
    · exact (hC a b c' c hab hbc' hcc h.symm).symm
end JardenShami
