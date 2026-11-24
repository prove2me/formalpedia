-- Prove2me | solution 1 for GlobalTheory.VolPairExists.mat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:04.858581+00:00
-- url     : https://prove2.me/submissions/32cdab95-df01-43bc-b0f7-614f98bf1986

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
theorem _root_.solution : Function.Injective (UpqT.mat (P := P) (Q := Q)) := by
  intro a b h
  let a' : Formalism.UG.Upq P Q := a
  let b' : Formalism.UG.Upq P Q := b
  have h' : a'.1 = b'.1 := Units.ext h
  exact (Subtype.ext h' : a' = b')
end GlobalTheory.VolPairExists
