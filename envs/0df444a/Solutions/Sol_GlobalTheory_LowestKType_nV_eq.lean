-- Prove2me | solution 1 for GlobalTheory.LowestKType.nV_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:23.50309+00:00
-- url     : https://prove2.me/submissions/55770b22-ac2f-4a95-96b8-9e7973a1ccf1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LamGeoEqFormula
import Theorems.Thm_GlobalTheory_LowestKType_r_eq

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
theorem _root_.solution (h : D.Hyp) : D.nV = D.p + D.q + D.t := by
  unfold WeightData.nV
  rw [r_eq h]
end GlobalTheory.LowestKType
