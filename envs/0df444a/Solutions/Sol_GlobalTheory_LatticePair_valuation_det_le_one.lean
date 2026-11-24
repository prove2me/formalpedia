-- Prove2me | solution 1 for GlobalTheory.LatticePair.valuation_det_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:49.101798+00:00
-- url     : https://prove2.me/submissions/628ecc17-d8cf-4f54-83c1-af3d8a75f88e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum

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
theorem _root_.solution {A : GL (Fin n) k} (hA : IsInt A) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := by
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨A.1 i j, hA i j⟩
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = A.1 := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← hB, ← RingHom.map_det]
  exact B.det.2
end GlobalTheory.LatticePair
