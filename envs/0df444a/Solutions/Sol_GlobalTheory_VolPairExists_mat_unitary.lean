-- Prove2me | solution 1 for GlobalTheory.VolPairExists.mat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:48.96742+00:00
-- url     : https://prove2.me/submissions/e2637d50-0f08-474f-b91d-a3cea8ab450c

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
theorem _root_.solution (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := by
  have hb := (b : Formalism.UG.Upq P Q).2
  exact hb
end GlobalTheory.VolPairExists
