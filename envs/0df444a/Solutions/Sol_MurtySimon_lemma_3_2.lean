-- Prove2me | solution 1 for MurtySimon.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:17:41.824679+00:00
-- url     : https://prove2.me/submissions/a8f15db1-bf21-43b4-bbbb-dab2b063ba01

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
public import Theorems.Thm_MurtySimon_exists_maximal_extension
public import Theorems.Thm_MurtySimon_isEdgeMatching_singleton
public import Theorems.Thm_MurtySimon_pieces_nonneg
public import Theorems.Thm_MurtySimon_card_LC0_split
public import Theorems.Thm_MurtySimon_comp_count
public import Theorems.Thm_MurtySimon_mem_Lt


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (hG : IsCritical G) (heq : EqCase G) (C : (aux G ∅).ConnectedComponent)
    (hC : 1 ≤ cA G ∅ C + cB G ∅ C) :
    cA G ∅ C = cB G ∅ C + 1 ∧
      ∀ N, IsEdgeMatching G N → #((LC0 C).filter (· ∈ N)) ≤ 1 := by
  have hle := (comp_count ∅ C).1
  -- for a maximal `M`, the left vertices of `C` in `M` number at most `cA - cB`
  have hmaxM : ∀ M, IsMaximalEdgeMatching G M → #((LC0 C).filter (· ∈ M)) + cB G ∅ C ≤ cA G ∅ C :=
    fun M hmax => by
      have h1 := pieces_nonneg hG heq hmax C
      have h2 := card_LC0_split M C
      omega
  have hext : ∀ N, IsEdgeMatching G N → #((LC0 C).filter (· ∈ N)) + cB G ∅ C ≤ cA G ∅ C := by
    intro N hN
    obtain ⟨M, hNM, hmax⟩ := exists_maximal_extension hN
    have h1 : (LC0 C).filter (· ∈ N) ⊆ (LC0 C).filter (· ∈ M) := fun e he =>
      mem_filter.2 ⟨(mem_filter.1 he).1, hNM (mem_filter.1 he).2⟩
    have := card_le_card h1
    have := hmaxM M hmax
    omega
  have hge : cB G ∅ C ≤ cA G ∅ C := by
    have := hext ∅ ⟨by simp, by simp⟩
    omega
  have heqA : cA G ∅ C = cB G ∅ C + 1 := by
    by_contra hne
    have hAB : cA G ∅ C = cB G ∅ C := by omega
    have hpos : 0 < #(LC0 C) := by
      have : #(LC0 C) = cA G ∅ C := rfl
      omega
    obtain ⟨e, he⟩ := card_pos.1 hpos
    have h1 := hext {e} (isEdgeMatching_singleton (mem_Lt.1 (mem_filter.1 he).1).1)
    have h2 : 1 ≤ #((LC0 C).filter (· ∈ ({e} : Finset (Sym2 V)))) :=
      card_pos.2 ⟨e, mem_filter.2 ⟨he, mem_singleton_self e⟩⟩
    omega
  refine ⟨heqA, fun N hN => ?_⟩
  have := hext N hN
  omega
end MurtySimon
