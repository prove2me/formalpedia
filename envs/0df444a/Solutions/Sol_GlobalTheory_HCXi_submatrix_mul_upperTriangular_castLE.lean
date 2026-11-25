-- Prove2me | solution 1 for GlobalTheory.HCXi.submatrix_mul_upperTriangular_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:59:31.843847+00:00
-- url     : https://prove2.me/submissions/1153e7b5-aed0-4c54-b82d-17121f01d6b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMul

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
theorem _root_.solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin m) ℂ) {j : ℕ} (hj : j ≤ m) (hu : u.BlockTriangular id) :
    (A * u).submatrix id (Fin.castLE hj) =
      A.submatrix id (Fin.castLE hj) * u.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
  ext i b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ?_ ?_ ?_ ?_
  · intro a _ c _ h
    exact Fin.castLE_injective hj h
  · intro a _
    exact Finset.mem_univ _
  · intro c _ hc
    have hlt : Fin.castLE hj b < c := by
      by_contra hle
      apply hc
      have h1 : c.val ≤ b.val := by
        have := not_lt.mp hle
        exact this
      refine ⟨⟨c.val, lt_of_le_of_lt h1 b.2⟩, by simp, ?_⟩
      ext
      simp
    rw [hu (show id (Fin.castLE hj b) < id c from hlt), mul_zero]
  · intro a _
    rfl
end GlobalTheory.HCXi
