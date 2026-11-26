-- Prove2me | solution 1 for HajnalSzemeredi.hajnal_szemeredi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:45.754253+00:00
-- url     : https://prove2.me/submissions/d5c806b1-aeef-4012-a507-165c2d46f82a

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_HajnalSzemeredi
public import Definitions.Def_HajnalSzemeredi_Solution
public import Theorems.Thm_HajnalSzemeredi_hajnalSzemeredi


set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi
namespace HajnalSzemeredi
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i j : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card ≤
        (Finset.univ.filter fun v => C v = j).card + 1 := by
  obtain ⟨C, hC⟩ := hajnalSzemeredi G r h
  exact ⟨C, fun i j => by convert hC i j⟩
end HajnalSzemeredi
