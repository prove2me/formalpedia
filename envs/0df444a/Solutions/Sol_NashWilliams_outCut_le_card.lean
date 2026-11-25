-- Prove2me | solution 1 for NashWilliams.outCut_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:31:51.356289+00:00
-- url     : https://prove2.me/submissions/6be80c4e-841e-4afe-9a33-88cb3270c070

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_mk_edgeEnds

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
open Classical
namespace NashWilliams
theorem _root_.solution [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (o : G.edgeSet → Bool)
    (S : Finset V) :
    outCut (edgeEnds G) o S ≤
      ((S ×ˢ Sᶜ).filter fun q : V × V => (toDigraph G o).Adj q.1 q.2).card := by
  classical
  unfold outCut
  let f : G.edgeSet → V × V := fun e => if o e then edgeEnds G e else (edgeEnds G e).swap
  have hf : ∀ e, s((f e).1, (f e).2) = e := by
    intro e
    by_cases ho : o e
    · simp only [f, ho, ↓reduceIte]
      exact mk_edgeEnds G e
    · simp only [f, ho, Bool.false_eq_true, ↓reduceIte, Prod.fst_swap, Prod.snd_swap]
      rw [Sym2.eq_swap, mk_edgeEnds]
  refine card_le_card_of_injOn f (fun e he => ?_) (fun e _ e' _ hee => ?_)
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at he
    simp only [coe_filter, mem_product, mem_compl, Set.mem_ofPred_eq]
    by_cases ho : o e
    · simp only [ho, ↓reduceIte] at he
      refine ⟨⟨by simp [f, ho, he.1], by simp [f, ho, he.2]⟩, e, by simp [f, ho]⟩
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at he
      refine ⟨⟨by simp [f, ho, he.1], by simp [f, ho, he.2]⟩, e, by simp [f, ho]⟩
  · apply Subtype.ext
    rw [← hf e, ← hf e', hee]
end NashWilliams
