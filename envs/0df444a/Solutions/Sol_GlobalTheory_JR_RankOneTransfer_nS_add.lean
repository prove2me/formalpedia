-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.nS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:09:41.206794+00:00
-- url     : https://prove2.me/submissions/1d8aed77-c10f-4cf3-b336-ead46178b2a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeylStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventuallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleOrbitalFourierRankOneTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.RankOneTransfer
namespace GlobalTheory.JR.RankOneTransfer
theorem _root_.solution {k : Type} [CommRing k] (a b : k) : nS (a + b) = nS a * nS b := by
  apply Subtype.ext
  show !![1, a + b; 0, 1] = !![1, a; 0, 1] * !![1, b; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]
end GlobalTheory.JR.RankOneTransfer
