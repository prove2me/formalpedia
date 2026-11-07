-- Prove2me | solution 1 for KarpPapadimitriou.Facial.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:02:17.184738+00:00
-- url     : https://prove2.me/submissions/bc237369-27bc-4cae-b637-f39c120e43ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription
import Theorems.Thm_KarpPapadimitriou_Facial_notMem_DLang_iff_lt_on_hull
import Theorems.Thm_KarpPapadimitriou_Facial_lt_on_hull_iff_lt_on_system
import Theorems.Thm_KarpPapadimitriou_Facial_lt_on_system_iff_basic_dual
import Theorems.Thm_KarpPapadimitriou_Facial_basicDualLang_mem_NP

open CookPvsNP ProjSchedTW.Complexity KarpPapadimitriou.Facial

theorem solution (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (hNP : tripleLang C F ∈ NP BSym) :
    DLang C ∈ coNP BSym := by
  show (DLang C)ᶜ ∈ NP BSym
  convert basicDualLang_mem_NP C F hF hs hNP using 1
  ext w
  constructor
  · intro hw z hz c k hwe hS
    subst hwe
    exact (lt_on_system_iff_basic_dual C F hF hs z hz hS c k).1
      ((lt_on_hull_iff_lt_on_system C F hF z hz c k).1
        ((notMem_DLang_iff_lt_on_hull C z hz c k).1 hw))
  · intro hw hmem
    obtain ⟨z, hz, c, k, ⟨x, hx, hkx⟩, rfl⟩ := hmem
    have hS : (C.S z).Nonempty := ⟨x, hx⟩
    have h := (notMem_DLang_iff_lt_on_hull C z hz c k).2
      ((lt_on_hull_iff_lt_on_system C F hF z hz c k).2
        ((lt_on_system_iff_basic_dual C F hF hs z hz hS c k).2 (hw z hz c k rfl hS)))
    exact h ⟨z, hz, c, k, ⟨x, hx, hkx⟩, rfl⟩
