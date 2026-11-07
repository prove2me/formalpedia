-- Prove2me | solution 1 for KarpPapadimitriou.Facial.corollary_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:02:18.041191+00:00
-- url     : https://prove2.me/submissions/90319fe3-ca3b-436e-8bcc-b9f8a411436d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription
import Theorems.Thm_KarpPapadimitriou_Facial_theorem_1
import Theorems.Thm_CookPvsNP_mem_NP_of_polyReducible

open CookPvsNP ProjSchedTW.Complexity KarpPapadimitriou.Facial

theorem solution (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (hNPC : NPComplete (DLang C)) (hNP : tripleLang C F ∈ NP BSym) :
    ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], NP Sym = coNP Sym := by
  intro Sym _ _
  have hco : (DLang C)ᶜ ∈ NP BSym := theorem_1 C F hF hs hNP
  -- every NP language over `Sym` is in coNP
  have key : ∀ L : Lang Sym, L ∈ NP Sym → L ∈ coNP Sym := by
    intro L hL
    obtain ⟨f, hf, hfL⟩ := hNPC.2 Sym L hL
    show Lᶜ ∈ NP Sym
    refine mem_NP_of_polyReducible Lᶜ (DLang C)ᶜ ⟨f, hf, fun x => ?_⟩ hco
    simp only [Set.mem_compl_iff, hfL x]
  ext L
  constructor
  · exact key L
  · intro hL
    have h := key Lᶜ hL
    simpa [coNP] using h
