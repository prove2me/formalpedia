-- Prove2me | solution 1 for GlobalTheory.LatticePair.isInt_mul_KO_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:45.137816+00:00
-- url     : https://prove2.me/submissions/7b4d7b77-e6c4-49a8-a508-bf0852fbd602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum
import Theorems.Thm_GlobalTheory_LatticePair_isInt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.LatticePair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.LatticePair
theorem _root_.solution {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (A * κ) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul hA h.1⟩
  have := isInt_mul hA h.2
  rwa [mul_inv_cancel_right] at this
end GlobalTheory.LatticePair
