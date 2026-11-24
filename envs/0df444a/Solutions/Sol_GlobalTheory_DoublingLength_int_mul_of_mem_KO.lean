-- Prove2me | solution 1 for GlobalTheory.DoublingLength.int_mul_of_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:34.006218+00:00
-- url     : https://prove2.me/submissions/9bb4a46f-9ad3-40c0-ba57-3dd6f3765625

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength

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
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.DoublingLength
theorem _root_.solution {g x : GL (Fin n) k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hx : x ∈ KO k (Fin n)) :
    ∀ i j, (g * x).1 i j ∈ 𝒪[k] := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hg i l) (((SplitFlip.mem_KO_iff x).1 hx).1 l j)
end GlobalTheory.DoublingLength
