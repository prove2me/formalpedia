-- Prove2me | solution 1 for MurtySimon.IsCrit.exists_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:57.236657+00:00
-- url     : https://prove2.me/submissions/b21417ea-b7f0-42df-82ed-b9ea147d5781

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_IsMid_symm


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
namespace IsCrit
theorem _root_.solution {x y : V} (h : IsCrit G s(x, y)) : ∃ u, IsMid G x y u := by
  obtain ⟨x', y', u, hf, hm⟩ := h
  rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨u, hm⟩
  · exact ⟨u, hm.symm⟩
end IsCrit
end MurtySimon
