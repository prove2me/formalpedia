-- Prove2me | solution 1 for LogSobolevMC.TwoPoint.dirichlet_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:34:45.916999+00:00
-- url     : https://prove2.me/submissions/39fb8276-911d-4990-bc15-1d680db3a439

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting
open LogSobolevMC.TwoPoint

open MarkovMixing

/-- Proof of Theorem A.1, p. 746: `ℰ(|f|, |f|) ≤ ℰ(f, f)` for every real function `f`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π (fun x => |f x|) (fun x => |f x|) ≤ LogSobolevMC.ChiSquare.dirichlet K π f f := by


  unfold LogSobolevMC.ChiSquare.dirichlet
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_right _ (hπpos x).le
  simp only [Matrix.mulVec, dotProduct]
  have hh : (∑ y, K x y * f y) * f x ≤
      (∑ y, K x y * |f y|) * |f x| := by
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y hy
    have h := mul_le_mul_of_nonneg_left (le_abs_self (f y * f x)) (hK.1 x y)
    simpa only [abs_mul, mul_assoc] using h
  have hs : |f x| * |f x| = f x * f x := by
    nlinarith [sq_abs (f x)]
  nlinarith
#print axioms solution

