-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.truncatedFormalJet_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:30:48.681165+00:00
-- url     : https://prove2.me/submissions/3d63cc64-30d3-48c1-adf9-fde10ed43a54

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncatedLogMatrix_mulVec_coeff_eq_truncatedFormalJet

/-!
# Row-sum formula for coefficients of a truncated formal jet

The coefficient of the truncated formal jet of a weighted polynomial `P` at a row
exponent `rho.2` is the `rho`-th entry of the truncated logarithmic interpolation
matrix applied to the simplex coefficient vector of `P`, i.e. the finite sum
`∑ c, truncatedLogMatrix rho c * [X^c] P` over the (finitely many) columns.

This is the reverse direction of the already-proved theorem
`truncatedLogMatrix_mulVec_coeff_eq_truncatedFormalJet`: by definition of
`Matrix.mulVecLin` and `Matrix.mulVec`, the matrix-vector product is exactly that
finite sum.  Hence the statement follows immediately from the matrix identity.
-/

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.1)
        (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val) =
      ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T rho c *
          MvPolynomial.coeff (InterpolationMatrix.exponentVector c.1) P.val := by
  have h := congr_fun
    (truncatedLogMatrix_mulVec_coeff_eq_truncatedFormalJet
      K w0 v0 theta w H r T hw0 hv0 htheta hw hT P) rho
  rw [← h]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
