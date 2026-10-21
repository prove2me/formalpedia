-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.columnCombination_weightedSupport
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:54:19.807997+00:00
-- url     : https://prove2.me/submissions/c4009f46-8307-4061-a03c-3c78848d88e0

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

/-- A column combination is supported on columns of the weighted simplex, hence every monomial in
its support satisfies the weighted degree bound `H`. -/
theorem solution {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) :
    ∀ a ∈ (columnCombination w0 w H x).support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : ℝ) ≤ H := by
  classical
  intro a ha
  rw [MvPolynomial.mem_support_iff] at ha
  -- expand the coefficient of the finite column combination
  have hcoeff : (columnCombination w0 w H x).coeff a =
      ∑ c : InterpolationMatrix.Column w0 w H,
        x c * (if a = InterpolationMatrix.exponentVector c.1 then 1 else 0) := by
    simp only [columnCombination, columnMonomial]
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    by_cases h : a = InterpolationMatrix.exponentVector c.1 <;> simp [h, eq_comm]
  -- some nonzero summand must occur
  have hex : ∃ c : InterpolationMatrix.Column w0 w H,
      x c ≠ 0 ∧ a = InterpolationMatrix.exponentVector c.1 := by
    by_contra h
    apply ha
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hx : x c = 0
    · simp [hx]
    · have hne : a ≠ InterpolationMatrix.exponentVector c.1 := by
        intro he
        exact h ⟨c, hx, he⟩
      simp [hne]
  obtain ⟨c, -, rfl⟩ := hex
  -- the exponent vector of a column recovers the column's coordinates
  have hcoord : ∀ i : Fin (m + 1),
      InterpolationMatrix.exponentVector c.1 i = c.1 i := by
    intro i
    simp [InterpolationMatrix.exponentVector, Finsupp.equivFunOnFinite_symm_apply_apply]
  simp only [hcoord]
  -- columns are points of the weighted simplex
  have hc := c.2
  change c.1 ∈ (Fintype.piFinset (fun i =>
      Finset.range (⌊H / InterpolationMatrix.columnWeights w0 w i⌋₊ + 1))).filter
        (fun a => ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : ℝ) ≤ H) at hc
  exact (Finset.mem_filter.mp hc).2
