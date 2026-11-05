-- Prove2me | solution 1 for HadwigerConj.complete_graph_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:18.82809+00:00
-- url     : https://prove2.me/submissions/6021078a-fee1-4608-a9fa-b7f182205268

import Definitions.Def_HadwigerConj_Defs

open SimpleGraph HadwigerConj

/-- Hadwiger's assertion holds when the input graph is complete. -/
theorem solution (n t : ℕ)
    (h : ¬ HasCompleteMinor (completeGraph (Fin n)) (t + 1)) :
    (completeGraph (Fin n)).Colorable t := by
  classical
  by_cases hnt : n ≤ t
  · exact (show (completeGraph (Fin n)).Colorable n by simpa using
      (completeGraph (Fin n)).colorable_of_fintype).mono hnt
  · have htn : t + 1 ≤ n := by omega
    let f : Fin (t + 1) → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt htn⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext (congrArg (fun k : Fin n => k.val) hij)
    apply False.elim
    apply h
    refine ⟨fun i => {f i}, ?_, ?_, ?_⟩
    · intro i
      exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
    · intro i j hij
      exact Set.disjoint_singleton.mpr (hf.ne hij)
    · intro i j hij
      exact ⟨f i, rfl, f j, rfl, by simpa using hf.ne hij⟩
