-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_log_weight_grid_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:42:29.684797+00:00
-- url     : https://prove2.me/submissions/4444ed74-899b-40ec-9a97-45d2c2b5a172

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Total grid variation of the complex logarithmic weight is bounded
by the sum of record and elapsed-time variations. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω)
    (u : Nat → NNReal) (N : Nat) (hu : Monotone u) :
    (∑ i ∈ Finset.range N,
      ‖G L Psi alpha beta (u (i+1)) w-G L Psi alpha beta (u i) w‖) ≤
      |beta-alpha| * (runningSup L (u N) w-runningSup L (u 0) w) +
        ‖Psi alpha‖ * ((u N:Real)-(u 0:Real)) := by
  let U : NNReal → Real := fun t => runningSup L t w
  have hU : Monotone U := (runningSup_monotone_and_path_le L w).1
  have hTel (f : Nat → Real) (k : Nat) :
      (∑ i ∈ Finset.range k, (f (i+1)-f i)) = f k-f 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih]; ring
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (|beta-alpha| * (U (u (i+1))-U (u i)) +
          ‖Psi alpha‖*((u (i+1):Real)-(u i:Real))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hUi := sub_nonneg.mpr (hU (hu (Nat.le_succ i)))
      have hti : 0 ≤ (u (i+1):Real)-(u i:Real) :=
        sub_nonneg.mpr (by exact_mod_cast hu (Nat.le_succ i))
      rw [show G L Psi alpha beta (u (i+1)) w-G L Psi alpha beta (u i) w =
          Complex.I*((beta-alpha:Real):Complex)*
            ((U (u (i+1))-U (u i):Real):Complex) -
          (((u (i+1):Real)-(u i:Real)):Complex)*Psi alpha by
        unfold G U
        push_cast
        ring]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_I,one_mul]
      simp only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hUi,abs_of_nonneg hti]
      exact le_of_eq (by ring)
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
        hTel (fun i => U (u i)),hTel (fun i => (u i:Real))]
