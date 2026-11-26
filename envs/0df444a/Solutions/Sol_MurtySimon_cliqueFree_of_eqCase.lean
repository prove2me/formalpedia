-- Prove2me | solution 1 for MurtySimon.cliqueFree_of_eqCase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:21:21.043439+00:00
-- url     : https://prove2.me/submissions/ba9167d7-c0a9-4893-828e-8aefa887841b

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
public import Theorems.Thm_MurtySimon_lemma_3_2
public import Theorems.Thm_MurtySimon_lemma_3_3
public import Theorems.Thm_MurtySimon_IsMid_isCrit
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_isCrit
public import Theorems.Thm_MurtySimon_OnPath_ne
public import Theorems.Thm_MurtySimon_exists_onPath_of_triangle
public import Theorems.Thm_MurtySimon_mem_Rt


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (hG : IsCritical G) (heq : EqCase G) : G.CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  by_cases hR : (Rt G).Nonempty
  · obtain ⟨f, hf⟩ := hR
    set C := (aux G ∅).connectedComponentMk f
    have hB : 1 ≤ cB G ∅ C := card_pos.2 ⟨f, mem_filter.2 ⟨hf, rfl⟩⟩
    have hA := (lemma_3_2 hG heq C (by omega)).1
    obtain ⟨u, hu⟩ := lemma_3_3 hG heq C hA hB
    rcases hu a b hab with rfl | rfl <;> rcases hu a c hac with h | h <;>
      rcases hu b c hbc with h' | h'
    all_goals first
      | exact hab.ne (by simp_all)
      | exact hac.ne (by simp_all)
      | exact hbc.ne (by simp_all)
  · obtain ⟨g, hg⟩ := exists_onPath_of_triangle hG hab hac hbc.symm
    exact hR ⟨g, mem_Rt.2 hg.isCrit⟩
end MurtySimon
