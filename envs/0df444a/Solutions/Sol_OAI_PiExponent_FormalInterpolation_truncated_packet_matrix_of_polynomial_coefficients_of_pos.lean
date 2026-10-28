-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:17:54.119102+00:00
-- url     : https://prove2.me/submissions/adb0c10f-ba7f-4db6-9774-54908f4a8b65

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_sum_eq_column_sum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coordinates_mem_realWeightedSimplex
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open OAI.PiExponent.InterpolationMatrix

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (_hH : 0 < H)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : Column w0 w H => P.val.coeff (exponentVector c.1)) := by
  classical
  refine funext fun rho => ?_
  simp only [truncatedPolynomialPacket]
  have hexp := truncated_polynomial_jet_support_expansion
    (j := rho.1.val) r T P.val rho.2.val
  rw [hexp]
  have hv : ∀ i, 0 < columnWeights w0 w i := fun i => Fin.cases hw0 hw i
  have hcols : ∀ e ∈ P.val.support,
      ∃ c : Column w0 w H, exponentVector c.1 = e := by
    intro e he
    let a : Fin (m + 1) → ℕ := fun i => e i
    have ha : ∑ i, columnWeights w0 w i * (a i : ℝ) ≤ H := by
      simpa [a] using P.property e he
    have hmem := weighted_coordinates_mem_realWeightedSimplex
      (columnWeights w0 w) H hv a ha
    refine ⟨⟨a, hmem⟩, ?_⟩
    -- exponentVector a = Finsupp.equivFunOnFinite.symm a = e
    simp only [exponentVector, a]
    exact (Finsupp.equivFunOnFinite.symm_apply_apply e)
  have hsum := truncated_packet_support_sum_eq_column_sum
    K w0 v0 theta w H r T P.val hcols rho
  rw [hsum]
  simp only [Matrix.mulVecLin_apply, truncatedLogMatrix]
  rfl
