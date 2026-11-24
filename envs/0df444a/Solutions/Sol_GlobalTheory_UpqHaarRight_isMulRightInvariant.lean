-- Prove2me | solution 1 for GlobalTheory.UpqHaarRight.isMulRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:37.747088+00:00
-- url     : https://prove2.me/submissions/c5fb47b8-56da-4811-b05a-605fabb1b94d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Imports
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_UpqUnimodular_isMulRightInvariant_of_isHaarMeasure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.UpqHaarRight
namespace GlobalTheory.UpqHaarRight
theorem _root_.solution :
    ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  fun P Q μ hμ => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ hμ
end GlobalTheory.UpqHaarRight
