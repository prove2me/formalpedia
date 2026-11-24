-- Prove2me | solution 1 for GlobalTheory.JR.weil_repG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:20.10204+00:00
-- url     : https://prove2.me/submissions/7ab81980-fe8a-4391-980d-41c8036836fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourierStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlock
import Theorems.Thm_GlobalTheory_JR_WeilMix_rowMap_mul
import Theorems.Thm_GlobalTheory_JR_WeilMix_rowMap_one
import Theorems.Thm_GlobalTheory_JR_WeilMix_isTest_rowAct
import Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_mixedModelPartialFourierColumn
import Theorems.Thm_GlobalTheory_T_mixedModelPartialFourierColumn_twice_neg_column
import Theorems.Thm_GlobalTheory_T_mixedModelPartialFourier_linear
import Theorems.Thm_GlobalTheory_T_mixedModel_weylElement_eq_partialFourier
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.JR.WeilMix
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  intro F E _ _ _ _ _ r M ψ hψ
  have hT := GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn F E r M ψ hψ
  have hI := GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ
  have hL := GlobalTheory.T.mixedModelPartialFourier_linear F E r M ψ hψ
  have hW := GlobalTheory.T.mixedModel_weylElement_eq_partialFourier F E r M ψ hψ
  have hψc : IsLocallyConstant (fun x : F => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  have h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f := by
    intro f hf
    rw [hI _ (hT _ (hT _ hf)), hI _ hf]
    funext Y; simp [negB]
  refine ⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    exact hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))
  · intro f hf
    have : rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f := by
      funext Y; simp [rowAct, rowMap_one]
    simp only [weil, this]
    exact h4 f hf
  · intro g h f hf
    simp only [weil]
    rw [h4 _ (isTest_rowAct h _ (hT _ hf))]
    congr 3
    funext Y; simp [rowAct, rowMap_mul]
  · intro g c f f' hf hf'
    have hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b := by
      intro a b; funext Y; simp [rowAct]
    simp only [weil]
    rw [hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')),
      hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))),
      hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]
  · intro f hf
    refine ⟨fun t Y => ?_, ?_⟩
    · let ft : Gl r F → ℂ := fun Y => ψ (t * mom Y 0) * f Y
      have hft : IsTest ft := by
        refine ⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩
        simp only [mom, pow_zero, Matrix.one_mulVec]
        fun_prop
      have key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft := by
        funext Y
        obtain ⟨A, u, c, l⟩ := Y
        simp only [rowAct, rowMap, ptrB, nS, ft]
        congr 1
        funext b
        simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, mul_zero, add_zero,
          mul_one, zero_add, mom, pow_zero, Matrix.one_mulVec]
        have hu : (fun i => c i * t + u i) = t • c + u := by funext i; simp [mul_comm]
        rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c,
          AddChar.map_add_eq_mul]
        ring
      show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _
      rw [key, h4 ft hft]
    · show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _
      rw [hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]
      exact hW f hf
end GlobalTheory.JR
