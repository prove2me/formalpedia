-- Prove2me | solution 1 for GlobalTheory.HypRot.offN_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:59.597145+00:00
-- url     : https://prove2.me/submissions/d8f4ed31-60b9-4f29-8c84-ec220907a606

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
theorem _root_.solution (j k : Fin r) (u : ℂ) : offN j k (-u) = - offN j k u := by
  simp only [offN, star_neg, Matrix.single_neg, neg_add]
end GlobalTheory.HypRot
