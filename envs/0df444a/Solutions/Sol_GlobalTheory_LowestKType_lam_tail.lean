-- Prove2me | solution 1 for GlobalTheory.LowestKType.lam_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:21.859856+00:00
-- url     : https://prove2.me/submissions/96c74df1-76ee-4371-b173-9e838798f4db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LamGeoEqFormula

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
theorem _root_.solution (h : D.Hyp) (c : ℕ) : D.lam (D.p + c) = -D.b (D.j + c) := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.lam WeightData.p
  rw [if_neg (by omega)]
  congr 2
  omega
end GlobalTheory.LowestKType
