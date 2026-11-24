-- Prove2me | solution 1 for GlobalTheory.LowestKType.aPlus_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:19.14071+00:00
-- url     : https://prove2.me/submissions/3aa7e879-ee43-4305-bfa6-6c27dc7933d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LamGeoEqFormula
import Theorems.Thm_GlobalTheory_LowestKType_nV_cast
import Theorems.Thm_GlobalTheory_LowestKType_exists_half_r
import Theorems.Thm_GlobalTheory_LowestKType_weightData_t_odd

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
theorem _root_.solution (h : D.Hyp) (i : ℕ) : ∃ z : ℤ, D.aPlus i = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.lam i + D.e - w - 1 + i - D.p, ?_⟩
  unfold WeightData.aPlus
  rw [nV_cast h, hu, hw]
  push_cast
  ring
end GlobalTheory.LowestKType
