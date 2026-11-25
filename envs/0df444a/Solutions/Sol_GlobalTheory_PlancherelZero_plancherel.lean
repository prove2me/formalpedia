-- Prove2me | solution 1 for GlobalTheory.PlancherelZero.plancherel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:49.479999+00:00
-- url     : https://prove2.me/submissions/c7b4dc36-2913-46b1-8830-daa1d274f83d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale
import Theorems.Thm_GlobalTheory_PlancherelZero_kerK_eq
import Theorems.Thm_GlobalTheory_PlancherelZero_lintegral_sq_eq_ofReal
import Theorems.Thm_GlobalTheory_PlancherelZero_isTest_fourB
import Theorems.Thm_GlobalTheory_JR_SelfDualUniq_isTest_fourB
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt


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
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) :
    ∫⁻ y, ‖fourB μK (A.kerK ψ) f y‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μK := by
  haveI := hsd.1
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hB := kerK_eq A ψ
  have hP := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd μK
    hsd.1).2 (hB ▸ hsd) f hf
  rw [lintegral_sq_eq_ofReal μK (isTest_fourB A ψ hψ μK hsd hf), lintegral_sq_eq_ofReal μK hf, hB, hP]
end GlobalTheory.PlancherelZero
