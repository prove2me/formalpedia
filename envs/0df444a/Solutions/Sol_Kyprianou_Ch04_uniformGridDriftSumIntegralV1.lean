-- Prove2me | solution 1 for Kyprianou.Ch04.uniformGridDriftSumIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:26:58.329094+00:00
-- url     : https://prove2.me/submissions/2437ec8d-9c31-447e-9409-51e97158ca44

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- A finite grid's weighted drift sum is the integral of its cellwise constant weights. -/
theorem solution (T : NNReal) (n : ℕ) (H : NNReal → ℝ) :
    (∫ s in Ioc (0 : ℝ) (T : ℝ),
      ∑ i ∈ Finset.range (n+1),
        (Ioc ((T * (i : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal) : ℝ)
          ((T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal) : ℝ)).indicator
          (fun _ => H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal))) s) =
    ∑ i ∈ Finset.range (n+1),
      H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) *
      ((T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal -
        (T * (i : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal) := by
  let u := fun i : ℕ => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
  let D := Ioc (0 : ℝ) (T : ℝ)
  let E := fun i : ℕ => Ioc (u i : ℝ) (u (i+1) : ℝ)
  have hmono : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  have hsub (i : ℕ) (hi : i ∈ Finset.range (n+1)) : E i ⊆ D := by
    have hle : u (i+1) ≤ T := by
      dsimp [u]
      rw [div_le_iff₀ (by positivity)]
      gcongr
      exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    intro x hx
    exact ⟨(u i).coe_nonneg.trans_lt hx.1,hx.2.trans (by exact_mod_cast hle)⟩
  change (∫ s in D, ∑ i ∈ Finset.range (n+1),
    (E i).indicator (fun _ => H (u i)) s) = _
  rw [integral_finsetSum _ (fun i hi =>
    (integrable_const (H (u i))).indicator measurableSet_Ioc)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (hsub i hi),setIntegral_const]
  simp only [E,measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr
    (show (u i : ℝ) ≤ (u (i+1) : ℝ) from by exact_mod_cast hmono (Nat.le_succ i))),smul_eq_mul]
  exact mul_comm _ _
