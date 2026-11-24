-- Prove2me | solution 1 for GlobalTheory.PlancherelZero.isTest_fourB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:18.416377+00:00
-- url     : https://prove2.me/submissions/edb371f4-4a14-474f-8439-7f84c327925c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale
import Theorems.Thm_GlobalTheory_PlancherelZero_kerK_eq
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_selfDual_measure_exists_unique_fourier_inversion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.PlancherelZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable [Unram F E]
namespace GlobalTheory.PlancherelZero
theorem _root_.solution (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) : IsTest (fourB μK (A.kerK ψ) f) := by
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  rw [kerK_eq A ψ]
  exact (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd).2 μK hsd.1 f hf
end GlobalTheory.PlancherelZero
