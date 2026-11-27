-- Prove2me | solution 1 for Kyprianou.Ch04.doubleFiniteMartingaleMaximalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:36:42.619435+00:00
-- url     : https://prove2.me/submissions/f73d06ec-ba94-40fc-a0ae-bd110343b2f3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMartingaleAbsSupSubmartingaleV1
import Theorems.Thm_MeasureTheory_maximal_ineq_Lp_readable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two successive Doob estimates bound the rectangular grid maximum
in L2 by four times the terminal L2 norm. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F G : Filtration ℕ inferInstance)
    (M : ℕ → ℕ → Ω → ℝ) (n m : ℕ)
    (hF : ∀ j ≤ n, Martingale (M j) F P)
    (hG : Martingale (fun j => M j m) G P) :
    eLpNorm (fun w => (Finset.range (m+1)).sup'
      Finset.nonempty_range_add_one (fun i => (Finset.range (n+1)).sup'
        Finset.nonempty_range_add_one (fun j => |M j i w|))) 2 P ≤
      4 * eLpNorm (M n m) 2 P := by
  let A (i : ℕ) (w : Ω) := (Finset.range (n+1)).sup'
    Finset.nonempty_range_add_one (fun j => |M j i w|)
  have hA : Submartingale A F P :=
    Kyprianou.Ch04.finiteMartingaleAbsSupSubmartingaleV1 P F M n hF
  have hnn (i : ℕ) (w : Ω) : 0 ≤ A i w :=
    (abs_nonneg _).trans (Finset.le_sup' (f := fun j => |M j i w|)
      (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
  have h1 := MeasureTheory.maximal_ineq_Lp_readable hA hnn
    (by norm_num : (1 : ℝ) < 2) m
  have h2 := AvramDividend.Classical.avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
    hG (by norm_num : (1 : ℝ) < 2) n
  norm_num at h1 h2
  have h2' : eLpNorm (A m) 2 P ≤ 2 * eLpNorm (M n m) 2 P := by
    simpa [A,Real.norm_eq_abs] using h2
  refine h1.trans ?_
  calc
    2 * eLpNorm (A m) 2 P ≤ 2 * (2 * eLpNorm (M n m) 2 P) := by gcongr
    _ = _ := by rw [← mul_assoc]; norm_num
