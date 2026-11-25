-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.norm_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:41.565578+00:00
-- url     : https://prove2.me/submissions/f4f217e7-73f6-42f1-bfc1-9ccaf7bfedb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
open TensorProduct Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (B : Basis (Fin 2) R S) (hB : B 0 = 1) {a b : R}
    (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) (r s : R) :
    Algebra.norm R (algebraMap R S r + algebraMap R S s * B 1)
      = r * (r + s * a) - s * b * s := by
  have : (algebraMap R S r + algebraMap R S s * B 1) * B 1
      = algebraMap R S (s * b) + algebraMap R S (r + s * a) * B 1 := by
    simp only [map_add, map_mul]
    linear_combination (algebraMap R S s) * hab
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hB, mul_one, this, repr_coord_zero B hB,
    repr_coord_zero B hB, repr_coord_one B hB, repr_coord_one B hB]
end GlobalTheory.QuadraticEtale
