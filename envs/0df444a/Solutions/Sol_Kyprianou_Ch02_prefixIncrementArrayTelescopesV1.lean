-- Prove2me | solution 1 for Kyprianou.Ch02.prefixIncrementArrayTelescopesV1
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:31:50.574437+00:00
-- url     : https://prove2.me/submissions/5d9133da-cd65-4eff-96a5-d6f065f1d673

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution (f : ℕ → ℝ) (n : ℕ) (k : Fin n) :
    (∑ i : Fin n, if i.val ≤ k.val then f (i.val+1)-f i.val else 0) =
      f (k.val+1)-f 0 := by
  have aux (m : ℕ) (hm : m ≤ n) : (∑ i : Fin n, if i.val < m then f (i.val+1)-f i.val else 0) = f m - f 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hmn : m < n := by omega
      let j : Fin n := ⟨m,hmn⟩
      have split : ∀ i : Fin n, (if i.val < m+1 then f (i.val+1)-f i.val else 0) = (if i.val < m then f (i.val+1)-f i.val else 0) + (if i=j then f (m+1)-f m else 0) := by
        intro i; by_cases hij : i=j
        · subst i; simp [j]
        · have hne : i.val ≠ m := fun e => hij (Fin.ext e)
          simp [hij, show (i.val < m+1) ↔ i.val < m by omega]
      simp_rw [split]; rw [Finset.sum_add_distrib, ih (by omega)]; simp
  simpa [Nat.lt_succ_iff] using aux (k.val+1) k.isLt
