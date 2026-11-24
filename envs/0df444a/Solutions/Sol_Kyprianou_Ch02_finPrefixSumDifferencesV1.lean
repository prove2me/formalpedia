-- Prove2me | solution 1 for Kyprianou.Ch02.finPrefixSumDifferencesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:23:08.809813+00:00
-- url     : https://prove2.me/submissions/510cac27-6451-49f5-b4fc-5c9cd0bc7d8f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (n : ℕ) (a : Fin (n+1) → ℝ) (h0 : a 0 = 0) (j : Fin (n+1)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j.val),
      (a i.succ - a i.castSucc)) = a j := by
  induction j using Fin.induction with
  | zero => simp [h0]
  | succ i ih =>
    have he : Finset.univ.filter (fun k : Fin n => k.val < i.succ.val) =
        insert i (Finset.univ.filter (fun k : Fin n => k.val < i.castSucc.val)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc]
      rw [Fin.ext_iff]
      omega
    rw [he, Finset.sum_insert (by simp), ih]
    ring
