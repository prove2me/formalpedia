-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.lam_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:25.133288+00:00
-- url     : https://prove2.me/submissions/c339e064-8bb2-42a2-bba3-c7b34eecae12

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
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_lam_comb
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_lam_zero
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_inI_sum

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
theorem _root_.solution [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hμ : μK.IsAddHaarMeasure) (a : A.K) {ι : Type} (s : Finset ι) (r : ι → ℂ)
    (Φ : ι → SpecialLinearGroup (Fin 2) A.K → ℂ) (h : ∀ i ∈ s, A.InI (Φ i)) (c : F) (hc : c ≠ 0) :
    A.abelian₂ μK ψ a (fun g => ∑ i ∈ s, r i * Φ i g) c = ∑ i ∈ s, r i * A.abelian₂ μK ψ a (Φ i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lam_zero F E A μK ψ a c
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, A.InI (Φ j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have := lam_comb F E A ψ hψ μK hμ a (fun g => ∑ j ∈ s, r j * Φ j g) (Φ i) (r i)
      (inI_sum A s r Φ hs) (h i (Finset.mem_insert_self i s)) c hc
    rw [Finset.sum_insert hi, ← ih hs, add_comm, ← this]
    congr 1
    funext g
    rw [Finset.sum_insert hi, add_comm]
end GlobalTheory.JR.RankOneTransfer
