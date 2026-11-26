-- Prove2me | solution 1 for HajnalSzemeredi.degLe_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:47.7318+00:00
-- url     : https://prove2.me/submissions/4c24bb64-b467-4c72-9f05-ff8b7140abe1

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_HajnalSzemeredi_Final
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} [Fintype V]
namespace HajnalSzemeredi
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (h : ∀ v, G.degree v ≤ r) :
    DegLe G univ r := by
  intro v _
  refine le_trans (card_le_card fun w hw => ?_) ((G.card_neighborFinset_eq_degree v).le.trans (h v))
  rw [SimpleGraph.mem_neighborFinset]
  exact (mem_nbr.mp hw).2
end HajnalSzemeredi
