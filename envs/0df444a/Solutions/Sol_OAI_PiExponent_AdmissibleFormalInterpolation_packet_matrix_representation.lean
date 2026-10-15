-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.packet_matrix_representation
-- status  : ACCEPTED   (disprove)
-- author  : @queelius
-- created : 2026-10-15T09:53:23.767529+00:00
-- url     : https://prove2.me/submissions/36f9c4b0-3f33-4e9b-b1af-312b1d1cce2d

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

/-
Directed by Alexander Richard Towell (queelius); counterexample and Lean implementation by Codex.
Concrete counterexample to Prove2Me target
54baace5-ae79-4d4f-a1fc-6fb436eda073, packet_matrix_representation.
This certificate addresses the archived platform reformulation. It does not
assert that the stronger upstream formal-packet bridge is false.
-/

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.InterpolationMatrix

private noncomputable def counterexamplePolynomial : WeightedPolynomial (m := 1) 3 (fun _ => 1) 2 := by
  classical
  refine ⟨MvPolynomial.X 1, ?_⟩
  intro a ha
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  norm_num [columnWeights, Fin.sum_univ_succ]

private noncomputable def counterexampleRow : Row (m := 1) 1 1 1 (fun _ => 1) 2 := by
  refine ⟨0, ![1, 0], ?_⟩
  norm_num [strictWeightedSimplex, realWeightedSimplex, rowWeights,
    Fintype.mem_piFinset, Fin.forall_fin_succ, Fin.sum_univ_succ]

private theorem column_zero (c : Column (m := 1) 3 (fun _ => 1) 2) : c.val 0 = 0 := by
  have h := (Finset.mem_filter.mp c.property).2
  change (∑ i : Fin 2, columnWeights 3 (fun _ : Fin 1 => 1) i * (c.val i : ℝ)) ≤ 2 at h
  norm_num [columnWeights, Fin.sum_univ_succ] at h
  have hn := Nat.cast_nonneg (α := ℝ) (c.val 1)
  have hc : (c.val 0 : ℝ) < 1 := by linarith
  have hcNat : c.val 0 < 1 := by exact_mod_cast hc
  omega

private theorem truncated_one : truncatedLog 1 = 0 := by
  ext n
  simp [truncatedLog, PowerSeries.coeff_log]

private theorem matrix_row_zero (c : Column (m := 1) 3 (fun _ => 1) 2) :
    truncatedLogMatrix (m := 1) 1 3 1 1 (fun _ => 1) 2 (fun _ => 0) (fun _ => 1) counterexampleRow c = 0 := by
  classical
  simp only [truncatedLogMatrix, matrix, entry, monomialImage]
  simp [counterexampleRow, column_zero c, truncated_one, exponentVector, MvPolynomial.coeff_X_pow]
  split_ifs <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_zero]

private theorem row_exponent :
    exponentVector counterexampleRow.2.val = Finsupp.cons 1 (0 : Fin 1 →₀ ℕ) := by
  ext i
  fin_cases i <;> simp [exponentVector, counterexampleRow, Finsupp.cons]

private theorem lift_log_coefficient :
    MvPowerSeries.coeff (Finsupp.cons 1 (0 : Fin 1 →₀ ℕ))
      (liftLogSeries 1 (PowerSeries.log ℂ)) = 1 := by
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp [liftLogSeries, PowerSeries.coeff_log]

private theorem packet_row_one :
    packetMap (m := 1) 1 3 1 1 (fun _ => 1) 2 (fun _ => 0) counterexamplePolynomial counterexampleRow = 1 := by
  classical
  simp only [packetMap, row_exponent]
  simp [counterexamplePolynomial, formalJet, counterexampleRow, MvPolynomial.aeval_X]
  change MvPowerSeries.coeff (Finsupp.cons 1 (0 : Fin 1 →₀ ℕ))
    (MvPowerSeries.X (1 : Fin 2) + liftLogSeries 1 (PowerSeries.log ℂ)) = 1
  have hne : Finsupp.cons 1 (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro h
    have h0 := congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
    norm_num [Finsupp.cons] at h0
  simp [map_add, lift_log_coefficient, MvPowerSeries.coeff_X, hne]

theorem solution :
    ¬ (∀ {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
      (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
      (_hw0 : 0 < w0) (_hv0 : 0 < v0) (_htheta : 0 < theta)
      (_hw : ∀ i, 0 < w i)
      (_hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
      (P : WeightedPolynomial w0 w H),
      ∃ x : InterpolationMatrix.Column w0 w H → ℂ,
        packetMap K w0 v0 theta w H r P =
          (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x) := by
  classical
  intro h
  obtain ⟨x, hx⟩ := h (m := 1) 1 3 1 1 (fun _ => 1) 2 (fun _ => 0) (fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (by intro i; norm_num)
    (by intro i; norm_num) counterexamplePolynomial
  have hrow := congrFun hx counterexampleRow
  rw [packet_row_one] at hrow
  have hz :
      ((truncatedLogMatrix (m := 1) 1 3 1 1 (fun _ => 1) 2 (fun _ => 0) (fun _ => 1)).mulVecLin x)
        counterexampleRow = 0 := by
    simp [Matrix.mulVec, dotProduct, matrix_row_zero]
  rw [hz] at hrow
  norm_num at hrow

