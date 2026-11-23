-- Prove2me | solution 1 for GlobalTheory.LowestKType.nV_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:58.602859+00:00
-- url     : https://prove2.me/submissions/7bc2812a-caae-4bfb-b940-d565df629cd8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LamGeoEqFormula
import Theorems.Thm_GlobalTheory_LowestKType_nV_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LowestKType
open Formalism.IndefR.IndefiniteWeightData Formalism.IndefR.IndefiniteWeightData.WeightData
variable {D : WeightData}
namespace GlobalTheory.LowestKType
theorem _root_.solution (h : D.Hyp) : (D.nV : ℚ) = D.p + D.q + D.t := by
  rw [nV_eq h]; push_cast; ring
end GlobalTheory.LowestKType
