-- Prove2me | solution 1 for GlobalTheory.isMulRightInvariant_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:51.859794+00:00
-- url     : https://prove2.me/submissions/70bd6149-0d3a-4c5a-83c4-abbc87c05050

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_eq_smul_haarProb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {K}
namespace GlobalTheory
theorem _root_.solution (μ : Measure K) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rw [eq_smul_haarProb μ]; infer_instance
end GlobalTheory
