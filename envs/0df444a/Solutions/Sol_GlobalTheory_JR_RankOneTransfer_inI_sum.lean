-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.inI_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:06.495339+00:00
-- url     : https://prove2.me/submissions/2d9d6219-b2fd-4d19-8b47-7fd56d1f00f3

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
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_inI_comb
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_inI_zero

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.RankOneTransfer
theorem _root_.solution (A : Et F E) {ι : Type} (s : Finset ι) (r : ι → ℂ) (Φ : ι → SpecialLinearGroup (Fin 2) A.K → ℂ)
    (h : ∀ i ∈ s, A.InI (Φ i)) : A.InI (fun g => ∑ i ∈ s, r i * Φ i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inI_zero F E A
  | insert i s hi ih =>
    have := inI_comb F E A (fun g => ∑ j ∈ s, r j * Φ j g) (Φ i) (r i)
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (h i (Finset.mem_insert_self i s))
    simpa [Finset.sum_insert hi, add_comm] using this
end GlobalTheory.JR.RankOneTransfer
