-- Prove2me | solution 1 for Kyprianou.Ch04.finiteMartingaleAbsSupSubmartingaleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:39:51.467627+00:00
-- url     : https://prove2.me/submissions/d7c29e29-275c-4511-9e98-523eea15938a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rangeSupSuccRealV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The maximum of the absolute values of finitely many real martingales
is a nonnegative submartingale. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℕ inferInstance)
    (M : ℕ → ℕ → Ω → ℝ) (n : ℕ) (hM : ∀ j ≤ n, Martingale (M j) F P) :
    Submartingale (fun i w => (Finset.range (n+1)).sup'
      Finset.nonempty_range_add_one (fun j => |M j i w|)) F P := by
  classical
  have ha (j : ℕ) (hj : j ≤ n) : Submartingale (fun i w => |M j i w|) F P := by
    have h := (hM j hj).submartingale.sup (hM j hj).neg.submartingale
    have he : M j ⊔ -(M j) = fun i w => |M j i w| := by
      funext i w
      change M j i w ⊔ (-M j i w) = |M j i w|
      by_cases hz : 0 ≤ M j i w
      · rw [sup_eq_left.mpr (by linarith),abs_of_nonneg hz]
      · rw [sup_eq_right.mpr (by linarith),abs_of_nonpos (by linarith)]
    rw [← he]
    exact h
  induction n with
  | zero => simpa using ha 0 le_rfl
  | succ n ih =>
    have hN := ih (fun j hj => hM j (hj.trans (Nat.le_succ n)))
      (fun j hj => ha j (hj.trans (Nat.le_succ n)))
    have h := (ha (n+1) le_rfl).sup hN
    have he : ((fun i w => |M (n+1) i w|) ⊔
        (fun i w => (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
          (fun j => |M j i w|))) = (fun i w =>
          (Finset.range (n+1+1)).sup' Finset.nonempty_range_add_one
            (fun j => |M j i w|)) := by
      funext i w
      change |M (n+1) i w| ⊔ (Finset.range (n+1)).sup'
        Finset.nonempty_range_add_one (fun j => |M j i w|) = _
      exact (Kyprianou.Ch04.rangeSupSuccRealV1 (fun j => |M j i w|) n).symm
    rw [← he]
    exact h
