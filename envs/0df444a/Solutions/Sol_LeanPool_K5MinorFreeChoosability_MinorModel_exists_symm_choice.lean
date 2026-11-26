-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.MinorModel.exists_symm_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:18.653535+00:00
-- url     : https://prove2.me/submissions/9fbc1546-46a4-41d5-9bef-3a2b61ac44e2

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable (M : MinorModel G H)
namespace LeanPool.K5MinorFreeChoosability.MinorModel
theorem _root_.solution :
    ∃ cd : H.Dart → G.Dart, (∀ e, (cd e).fst ∈ M.branch e.fst) ∧
      (∀ e, (cd e).snd ∈ M.branch e.snd) ∧ ∀ e, cd e.symm = (cd e).symm := by
  classical
  have hf : ∀ e : H.Dart, ∃ d : G.Dart, d.fst ∈ M.branch e.fst ∧ d.snd ∈ M.branch e.snd := by
    intro e
    obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent e.fst e.snd e.adj
    exact ⟨⟨(u, v), huv⟩, hu, hv⟩
  choose f hf1 hf2 using hf
  refine ⟨fun e => if WellOrderingRel e.fst e.snd then f e else (f e.symm).symm, ?_, ?_, ?_⟩
  · intro e
    dsimp only
    split_ifs
    · exact hf1 e
    · exact hf2 e.symm
  · intro e
    dsimp only
    split_ifs
    · exact hf2 e
    · exact hf1 e.symm
  · intro e
    have hne : e.fst ≠ e.snd := e.adj.ne
    have hs1 : e.symm.fst = e.snd := rfl
    have hs2 : e.symm.snd = e.fst := rfl
    dsimp only
    rw [hs1, hs2, SimpleGraph.Dart.symm_symm]
    by_cases h : WellOrderingRel e.fst e.snd
    · simp [h, asymm h]
    · have h' : WellOrderingRel e.snd e.fst := by
        rcases trichotomous_of WellOrderingRel e.fst e.snd with h1 | h1 | h1
        · exact absurd h1 h
        · exact absurd h1 hne
        · exact h1
      simp [h, h']
end LeanPool.K5MinorFreeChoosability.MinorModel
