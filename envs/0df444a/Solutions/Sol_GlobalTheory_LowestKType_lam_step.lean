-- Prove2me | solution 1 for GlobalTheory.LowestKType.lam_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:20.988506+00:00
-- url     : https://prove2.me/submissions/e4f454a0-431d-463d-81e9-e1a2a0f943e2

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
theorem _root_.solution (h : D.Hyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.r) :
    (D.lam (i + 1) : ℚ) + 1 ≤ D.lam i := by
  have : D.lam (i + 1) + 1 ≤ D.lam i := h.2.2.2.2.2.1 i h1 h2
  exact_mod_cast this
end GlobalTheory.LowestKType
