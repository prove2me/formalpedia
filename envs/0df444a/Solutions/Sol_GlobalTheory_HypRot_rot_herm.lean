-- Prove2me | solution 1 for GlobalTheory.HypRot.rot_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:05.740227+00:00
-- url     : https://prove2.me/submissions/fcd51d4d-81d0-4a1f-877a-af1fea5f3ca9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations

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
theorem _root_.solution (j k : Fin r) (u : ℂ) : (rot j k u).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rot, offN, projP, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_star, star_one, smul_add]
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by simp
  have h34 : star (3 / 4 : ℂ) = 3 / 4 := by simp
  rw [h4, h34]
  abel
end GlobalTheory.HypRot
