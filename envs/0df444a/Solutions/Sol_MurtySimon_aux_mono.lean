-- Prove2me | solution 1 for MurtySimon.aux_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:33.546197+00:00
-- url     : https://prove2.me/submissions/28f14d2e-4d37-4ba4-8e17-f9703da13448

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_aux_adj

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
theorem _root_.solution {M N : Finset (Sym2 V)} (h : N ⊆ M) : aux G M ≤ aux G N := by
  intro e f hef
  rw [aux_adj] at hef ⊢
  rcases hef with hef | hef
  · exact Or.inl ⟨fun hN => hef.1 (h hN), hef.2⟩
  · exact Or.inr ⟨fun hN => hef.1 (h hN), hef.2⟩
end MurtySimon
