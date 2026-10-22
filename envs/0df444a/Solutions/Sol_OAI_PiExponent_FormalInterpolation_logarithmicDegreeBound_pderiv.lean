-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T09:26:48.106351+00:00
-- url     : https://prove2.me/submissions/d4234b19-a81e-452a-a955-2db611a79c10

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (k : Fin (m + 1)) :
    logarithmicDegreeBound w N (MvPolynomial.pderiv k F) := by
  classical
  intro a ha
  have hcoeff : MvPolynomial.coeff a (MvPolynomial.pderiv k F) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hsource : MvPolynomial.coeff (a + Finsupp.single k 1) F ≠ 0 :=
    (mul_ne_zero_iff.mp hcoeff).1
  let b : Fin (m + 1) →₀ Nat := a + Finsupp.single k 1
  have hsource_mem : b ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr (by simpa [b] using hsource)
  have hcoord : ∀ i, a i ≤ b i := by
    intro i
    simp only [b, Finsupp.add_apply]
    by_cases hik : i = k <;> simp [hik]
  have hsum : (∑ i, (w i : Real) * (a i : Real)) ≤
      ∑ i, (w i : Real) * (b i : Real) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcoord i)) (le_of_lt (hw i))
  exact hsum.trans (hF b hsource_mem)