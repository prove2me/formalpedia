-- Prove2me | solution 1 for HajnalSzemeredi.hajnalSzemeredi_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:55.727472+00:00
-- url     : https://prove2.me/submissions/f8b14c22-0847-4aff-9c3c-5cb0b1092fcd

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_HajnalSzemeredi_Final
public import Theorems.Thm_HajnalSzemeredi_degLe_univ
public import Theorems.Thm_HajnalSzemeredi_core
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} [Fintype V]
namespace HajnalSzemeredi
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (r s : ℕ)
    (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i, (univ.filter fun v => C v = i).card = s := by
  obtain ⟨c, hc⟩ := core _ G univ (range (r + 1)) r s rfl (card_range _)
    (by rw [card_univ, hcard]) (degLe_univ G h)
  have hlt : ∀ v, c v < r + 1 := fun v => mem_range.mp (hc.into v (mem_univ v))
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨c v, hlt v⟩) fun {u v} huv heq =>
    hc.proper u (mem_univ u) v (mem_univ v) huv (congrArg Fin.val heq), fun i => ?_⟩
  refine Eq.trans ?_ (hc.card i (mem_range.mpr i.isLt))
  congr 1
  ext v
  simp [cls, Fin.ext_iff]; rfl
end HajnalSzemeredi
