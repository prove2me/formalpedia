-- Prove2me | solution 1 for LittleLaw50.FiniteWindow.corollary_3b
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:39:14.54599+00:00
-- url     : https://prove2.me/submissions/97b52f1e-2b2a-4c8a-a184-895a89596992

import Mathlib
import Definitions.Def_LittleLaw50_FiniteWindow_Window
import Theorems.Thm_LittleLaw50_FiniteWindow_corollary_3a

open LittleLaw50.FiniteWindow

theorem solution {M K : ℕ} (a d : Fin M → ℝ) (c : Fin M → Fin K)
    (T : ℝ) (hT : 0 < T) (had : ∀ i, a i ≤ d i) :
    (∑ k, Lw (classItems c k) a d T) =
      (∑ k, lamw (classItems c k) a d T) *
        ∑ k, (lamw (classItems c k) a d T /
          ∑ k', lamw (classItems c k') a d T) * Ww (classItems c k) a d T := by
  have hnonneg : ∀ k, 0 ≤ lamw (classItems c k) a d T := by
    intro k
    exact div_nonneg (Nat.cast_nonneg _) hT.le
  by_cases hs : (∑ k, lamw (classItems c k) a d T) = 0
  · have hzero : ∀ k, lamw (classItems c k) a d T = 0 := by
      intro k
      have hk := Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ k)
      exact le_antisymm (by simpa only [hs] using hk) (hnonneg k)
    rw [hs, zero_mul]
    apply Finset.sum_eq_zero
    intro k _
    rw [corollary_3a a d c T hT had k, hzero k, zero_mul]
  · simp_rw [corollary_3a a d c T hT had]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    field_simp [hs] <;> ring

#print axioms solution
