-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.surjective_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:36.429796+00:00
-- url     : https://prove2.me/submissions/29ed8b52-3353-4bb2-ae78-5bedeaba9fdd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : Function.Surjective (frobenius (ModP (normInteger K) p) p) :=
  IsPerfectoidField.surjective_pow
end GroundTheory.PAdicHodge.IsPerfectoidField
