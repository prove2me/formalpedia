-- Prove2me | solution 1 for MurtySimon.aux_adj_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:32.252209+00:00
-- url     : https://prove2.me/submissions/556923dc-a793-4c76-8034-17379ed9a3c5

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
public import Theorems.Thm_MurtySimon_mem_Rt
public import Theorems.Thm_MurtySimon_mem_Lt
public import Theorems.Thm_MurtySimon_IsMid_isCrit
public import Theorems.Thm_MurtySimon_OnPath_isCrit
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_aux_adj


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} {e f : Sym2 V} (h : (aux G M).Adj e f) :
    (e ∈ Lt G M ∧ f ∈ Rt G ∧ OnPath G e f) ∨ (f ∈ Lt G M ∧ e ∈ Rt G ∧ OnPath G f e) := by
  rcases aux_adj.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨mem_Lt.2 ⟨h2.mem_edgeSet, h1⟩, mem_Rt.2 h2.isCrit, h2⟩
  · exact Or.inr ⟨mem_Lt.2 ⟨h2.mem_edgeSet, h1⟩, mem_Rt.2 h2.isCrit, h2⟩
end MurtySimon
