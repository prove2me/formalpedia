-- Prove2me | solution 1 for GlobalTheory.HypRot.rot_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:20.952655+00:00
-- url     : https://prove2.me/submissions/810ec18d-36eb-497c-8606-986f396f4fb3

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
    (rot j k u)⁻¹ = rot j k (-u) := Matrix.inv_eq_right_inv (rot_mul_neg h hu)
end GlobalTheory.HypRot
