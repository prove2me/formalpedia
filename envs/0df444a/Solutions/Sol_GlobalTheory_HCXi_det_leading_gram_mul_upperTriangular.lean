-- Prove2me | solution 1 for GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:55.897083+00:00
-- url     : https://prove2.me/submissions/031a178a-85ed-4a68-b222-d269c280e9b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMul
import Theorems.Thm_GlobalTheory_HCXi_submatrix_mul_upperTriangular_castLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
theorem _root_.solution :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  intro n m A u j hj hu
  have key : ∀ B : Matrix (Fin n) (Fin m) ℂ,
      (Bᴴ * B).submatrix (Fin.castLE hj) (Fin.castLE hj) =
        (B.submatrix id (Fin.castLE hj))ᴴ * B.submatrix id (Fin.castLE hj) := by
    intro B
    ext a b
    simp [Matrix.mul_apply]
  have hu' : (u.submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := by
    intro a b hab
    exact hu (show id (Fin.castLE hj b) < id (Fin.castLE hj a) from hab)
  rw [key, key, submatrix_mul_upperTriangular_castLE A u hj hu, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (u.submatrix (Fin.castLE hj) (Fin.castLE hj)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_upperTriangular hu']
  simp only [Matrix.submatrix_apply]
  rw [← map_prod Complex.normSq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring
end GlobalTheory.HCXi
