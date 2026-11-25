-- Prove2me | solution 1 for GlobalTheory.JR.HypJ.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:40.624284+00:00
-- url     : https://prove2.me/submissions/02e8f1e3-e3de-4582-a22d-b8b605e162bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourierStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TestFunctionLocallyInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypUnipotentTorusEquivarianceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeyl
import Theorems.Thm_GlobalTheory_T_fourierEtaleK_eq_integral_partialFourier
import Theorems.Thm_GlobalTheory_T_jHyp_unipotent_torus_equivariance
import Theorems.Thm_GlobalTheory_T_partialFourier_etaleKProd_locallyConstantCompactSupport
import Theorems.Thm_GlobalTheory_T_test_function_locally_invariant
import Theorems.Thm_GlobalTheory_TestFn_slice_test


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HypJ
namespace GlobalTheory.JR.HypJ
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  have hH : μK.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport F E A ψ hψ μK hH φ' hφ
  refine ⟨⟨?_, fun z s g => GlobalTheory.T.jHyp_unipotent_torus_equivariance F E A μK hH ψ φ' z s g⟩, ?_⟩
  · obtain ⟨U, hU, hk⟩ := GlobalTheory.T.test_function_locally_invariant A.K _ hT
    refine ⟨U, hU, fun g k hkU => ?_⟩
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := hk k hkU (t * g 1 0) (t * g 1 1)
    simp only at this
    have e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 =
        g 1 0 * k 0 0 + g 1 1 * k 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 =
        g 1 0 * k 0 1 + g 1 1 * k 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e1, e2]
    rw [← this]; congr 2 <;> ring
  · intro h
    have key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c := by
      intro c u
      have hG := GlobalTheory.TestFn.slice_test _ hT c
      have := hsd.2 _ hG u
      rw [← this]
      unfold Et.tilde fourB
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier F E A ψ hψ μK hH φ' hφ b c]
      unfold fourB Et.tilde Et.kerK
      rw [mul_comm u b]
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [key]
    congr 2
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
end GlobalTheory.JR.HypJ
