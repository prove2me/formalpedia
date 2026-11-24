-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.surjective_fontaineTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:25:03.469271+00:00
-- url     : https://prove2.me/submissions/c0b2c2d7-ca87-4a3c-9901-4806aae7d4e4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_frobenius

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
theorem _root_.solution : Function.Surjective (WittVector.fontaineTheta (normInteger K) p) :=
  _root_.surjective_fontaineTheta (surjective_frobenius p)
end GroundTheory.PAdicHodge.IsPerfectoidField
