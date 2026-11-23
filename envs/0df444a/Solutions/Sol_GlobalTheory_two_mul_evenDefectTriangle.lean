-- Prove2me | solution 1 for GlobalTheory.two_mul_evenDefectTriangle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:17.461166+00:00
-- url     : https://prove2.me/submissions/ca59ec2d-81aa-42e8-afb5-3f17d6a43ebc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicalFunctionOfHomomorphism

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℤ) : 2 * evenDefectTriangle n = n * (n - 1) := by
  unfold evenDefectTriangle
  exact Int.mul_ediv_cancel' (Int.even_mul_pred_self n).two_dvd
end GlobalTheory
