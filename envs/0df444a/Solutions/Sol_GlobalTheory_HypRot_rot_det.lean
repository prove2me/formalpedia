-- Prove2me | solution 1 for GlobalTheory.HypRot.rot_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:20.149463+00:00
-- url     : https://prove2.me/submissions/9d04a28f-925b-4940-8513-491bc97f803d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
import Theorems.Thm_GlobalTheory_HypRot_rot_mul_neg

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
theorem _root_.solution {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u).det ≠ 0 := (Matrix.isUnit_det_of_right_inverse (rot_mul_neg h hu)).ne_zero
end GlobalTheory.HypRot
