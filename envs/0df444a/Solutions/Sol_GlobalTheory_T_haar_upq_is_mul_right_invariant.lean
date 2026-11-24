-- Prove2me | solution 1 for GlobalTheory.T.haar_upq_is_mul_right_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:32.847162+00:00
-- url     : https://prove2.me/submissions/0249ae54-395e-44c5-895f-51c0daa0b028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariantStatement
import Theorems.Thm_GlobalTheory_UpqUnimodular_isMulRightInvariant_of_isHaarMeasure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.BasicNotions
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure <;> assumption)
end _root_.GlobalTheory.T
