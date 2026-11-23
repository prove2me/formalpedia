-- Prove2me | solution 1 for GlobalTheory.HypRot.projP_offN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:00.243993+00:00
-- url     : https://prove2.me/submissions/9a419be5-4cbb-465e-b990-dfd7dbd6c00e

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
theorem _root_.solution {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    projP j k * offN j k u = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]
end GlobalTheory.HypRot
