-- Prove2me | solution 1 for GlobalTheory.LowestKType.dTau_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:20.151858+00:00
-- url     : https://prove2.me/submissions/7f6827c1-b6ed-45dc-94b5-6124785506f9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LamGeoEqFormula
import Theorems.Thm_GlobalTheory_LowestKType_exists_half_r

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
theorem _root_.solution (h : D.Hyp) : ∃ z : ℤ, D.dTau = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  refine ⟨D.p - u - 1 - D.e, ?_⟩
  unfold WeightData.dTau
  rw [hu]; push_cast; ring
end GlobalTheory.LowestKType
