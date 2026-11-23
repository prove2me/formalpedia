-- Prove2me | solution 1 for GlobalTheory.HypRot.diag_rot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:59.481827+00:00
-- url     : https://prove2.me/submissions/06101581-a680-4546-bff7-9dfb16cee62d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
namespace HypRot
variable {r : ℕ}
private lemma diagonal_mul_single (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]
private lemma single_mul_diagonal (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]
end HypRot
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.HypRot
variable {r : ℕ}
namespace GlobalTheory.HypRot
theorem _root_.solution {j k : Fin r} (d : Fin r → ℂ) (hd : d j = - d k) (u : ℂ) :
    Matrix.diagonal d * rot j k u = rot j k (-u) * Matrix.diagonal d := by
  simp only [rot, offN, projP, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, diagonal_mul_single, single_mul_diagonal, star_neg, hd]
  simp only [mul_one, one_mul, neg_mul, mul_neg, neg_neg, mul_comm u (d k), mul_comm (star u) (d k)]
end GlobalTheory.HypRot
