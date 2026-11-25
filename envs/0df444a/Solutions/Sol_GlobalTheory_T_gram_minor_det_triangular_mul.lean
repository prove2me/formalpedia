-- Prove2me | solution 1 for GlobalTheory.T.gram_minor_det_triangular_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:57.966909+00:00
-- url     : https://prove2.me/submissions/d1b346a3-ffdb-4b35-a0b9-7702826c8313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMulStatement
import Theorems.Thm_GlobalTheory_HCXi_det_leading_gram_mul_upperTriangular


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  first | exact @GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular | exact GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular | (intros; apply GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular <;> assumption)
end _root_.GlobalTheory.T
