-- Prove2me | solution 1 for GlobalTheory.VolPairExists.mat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:05.500145+00:00
-- url     : https://prove2.me/submissions/d4e10d2f-4ce9-4a6a-bab7-373ecb7df53e

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
theorem _root_.solution (b c : UpqT P Q) : UpqT.mat (b * c) = UpqT.mat b * UpqT.mat c := rfl
end GlobalTheory.VolPairExists
