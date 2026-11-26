-- Prove2me | solution 1 for HajnalSzemeredi.hajnal_szemeredi_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:09.923116+00:00
-- url     : https://prove2.me/submissions/e34c8a8e-a27e-4b2f-be62-1d50cbc28c24

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_HajnalSzemeredi
public import Definitions.Def_HajnalSzemeredi_Solution
public import Theorems.Thm_HajnalSzemeredi_hajnalSzemeredi_exact


set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi
namespace HajnalSzemeredi
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card = s := by
  obtain ⟨C, hC⟩ := hajnalSzemeredi_exact G r s hcard h
  exact ⟨C, fun i => by convert hC i⟩
end HajnalSzemeredi
