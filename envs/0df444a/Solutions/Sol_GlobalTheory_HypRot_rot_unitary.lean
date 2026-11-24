-- Prove2me | solution 1 for GlobalTheory.HypRot.rot_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:22.34048+00:00
-- url     : https://prove2.me/submissions/2199d151-afc2-4273-829b-6d23531c770d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
import Theorems.Thm_GlobalTheory_HypRot_rot_mul_neg
import Theorems.Thm_GlobalTheory_HypRot_rot_herm
import Theorems.Thm_GlobalTheory_HypRot_diag_rot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.HypRot
variable {r : ℕ}
namespace GlobalTheory.HypRot
theorem _root_.solution {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1)
    (d : Fin r → ℂ) (hd : d j = - d k) :
    (rot j k u)ᵀ * Matrix.diagonal d * (rot j k u).map (starRingEnd ℂ) = Matrix.diagonal d := by
  have hT : (rot j k u)ᵀ = rot j k (star u) := by
    simp only [rot, offN, projP, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_single, star_star, smul_add]
    abel
  have hC : (rot j k u).map (starRingEnd ℂ) = (rot j k u)ᵀ := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    exact (rot_herm j k u).apply b a
  have hu' : star u * star (star u) = 1 := by rw [star_star, mul_comm]; exact hu
  rw [hC, hT, Matrix.mul_assoc, diag_rot d hd, ← Matrix.mul_assoc, rot_mul_neg h hu',
    Matrix.one_mul]
end GlobalTheory.HypRot
