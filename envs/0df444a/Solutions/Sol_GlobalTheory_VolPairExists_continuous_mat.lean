-- Prove2me | solution 1 for GlobalTheory.VolPairExists.continuous_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:56.48681+00:00
-- url     : https://prove2.me/submissions/595acdda-d6d8-432c-af65-16bf28f985e2

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.VolPairExists
variable {P Q : ℕ}
namespace GlobalTheory.VolPairExists
theorem _root_.solution : Continuous (UpqT.mat (P := P) (Q := Q)) := by
  exact Units.continuous_val.comp continuous_subtype_val
end GlobalTheory.VolPairExists
