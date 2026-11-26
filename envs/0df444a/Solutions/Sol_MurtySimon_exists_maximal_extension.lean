-- Prove2me | solution 1 for MurtySimon.exists_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:42.189639+00:00
-- url     : https://prove2.me/submissions/4f587e54-dbaf-4eed-ad21-952c2e406390

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {N : Finset (Sym2 V)} (hN : IsEdgeMatching G N) :
    ∃ M, N ⊆ M ∧ IsMaximalEdgeMatching G M := by
  set S := (univ : Finset (Finset (Sym2 V))).filter fun M => IsEdgeMatching G M ∧ N ⊆ M
  have hS : S.Nonempty := ⟨N, mem_filter.2 ⟨mem_univ _, hN, subset_refl _⟩⟩
  obtain ⟨M, hMS, hmax⟩ := exists_max_image S card hS
  obtain ⟨hM, hNM⟩ := (mem_filter.1 hMS).2
  refine ⟨M, hNM, hM, fun e he heM hins => ?_⟩
  have := hmax (insert e M) (mem_filter.2 ⟨mem_univ _, hins, hNM.trans (subset_insert _ _)⟩)
  rw [card_insert_of_notMem heM] at this
  omega
end MurtySimon
