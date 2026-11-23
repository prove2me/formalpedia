-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.det_mul_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:22.076412+00:00
-- url     : https://prove2.me/submissions/f49ac56e-7f43-4b09-afd9-e4ac3417747b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (σ : K →+* ℂ) (b : Basis (Fin 2) ℚ K) (h0 : b 0 = 1) (x y : K) :
    (b.det ![x, y] : ℝ) * (σ (b 1)).im = (σ y * conj (σ x)).im := by
  have hx : ∀ x : K, σ x = (b.repr x 0 : ℝ) + (b.repr x 1 : ℝ) * σ (b 1) := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    simp [h0, Rat.smul_def]
  rw [hx x, hx y, Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]
  ring
end GlobalTheory.QuadraticZeta
