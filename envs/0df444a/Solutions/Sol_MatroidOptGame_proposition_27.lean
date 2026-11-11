-- Prove2me | solution 1 for MatroidOptGame.proposition_27
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-10T10:56:17.968339+00:00
-- url     : https://prove2.me/submissions/7234121c-9940-4106-b987-7517a18f1f37

import Mathlib

theorem solution {α : Type*} (M : Matroid α) (B : Set α) (e : α) (hB : M.IsBase B)
    (he : e ∈ B) : (M.contract {e}).IsBase (B \ {e}) := by
  have hsub : ({e} : Set α) ⊆ B := Set.singleton_subset_iff.mpr he
  have hI : M.Indep {e} := hB.indep.subset hsub
  rw [hI.contract_isBase_iff]
  refine ⟨?_, Set.disjoint_sdiff_left⟩
  rwa [Set.sdiff_union_self, Set.union_eq_self_of_subset_right hsub]
