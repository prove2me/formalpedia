-- Prove2me | solution 1 for GlobalTheory.QuadNormBase.norm_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:37.125375+00:00
-- url     : https://prove2.me/submissions/7caa7123-ee76-4219-b81d-ac0d59955bb2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadNormBase
namespace GlobalTheory.QuadNormBase
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (B : Module.Basis (Fin 2) R A) (d : R) (h0 : B 0 = 1) (h1 : B 1 * B 1 = d • B 0) (x y : R) :
    Algebra.norm R (x • B 0 + y • B 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • B 0 + y • B 1) * B 0 = x • B 0 + y • B 1 := by rw [h0, mul_one]
  have e1 : (x • B 0 + y • B 1) * B 1 = (y * d) • B 0 + x • B 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, smul_smul, add_comm]
    congr 1
    rw [h0, one_mul]
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp
  ring
end GlobalTheory.QuadNormBase
