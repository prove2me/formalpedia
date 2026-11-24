-- Prove2me | solution 1 for GlobalTheory.FourKTest.fourK_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:11.783493+00:00
-- url     : https://prove2.me/submissions/67ffb0bc-2170-4aef-8fd1-312c5cd32178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppo
import Theorems.Thm_GlobalTheory_FourKTest_betaK_apply
import Theorems.Thm_GlobalTheory_FourKTest_betaK_isSymm
import Theorems.Thm_GlobalTheory_FourKTest_betaK_nondeg
import Theorems.Thm_GlobalTheory_FourKTest_secondCountable
import Theorems.Thm_GlobalTheory_FourKTest_psi_continuous
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
open GlobalTheory GlobalTheory.FourKTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.FourKTest
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  haveI := secondCountable A
  haveI : μK.IsAddHaarMeasure := hsd.1
  haveI : (μK.prod μK).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have key := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ (A.K × A.K) (betaK A) (betaK_isSymm A) (betaK_nondeg A hnd)).2
    (μK.prod μK) inferInstance φ' hφ
  have hψc := psi_continuous ψ hψ
  have heq : A.fourK μK ψ φ' = fourB (μK.prod μK) (fun x y => ψ (betaK A x y)) φ' := by
    funext p
    simp only [fourB, Et.fourK]
    rw [integral_prod]
    · refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
      refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
      simp only [Et.psiK, betaK_apply, map_add]
      congr 1
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_comm p.1, mul_comm c' p.1]
      ring
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hφ.1.continuous.mul (hψc.comp (IsModuleTopology.continuous_of_linearMap ((betaK A).flip p)))
      · exact hφ.2.mul_right
  rw [heq]; exact key
end GlobalTheory.FourKTest
