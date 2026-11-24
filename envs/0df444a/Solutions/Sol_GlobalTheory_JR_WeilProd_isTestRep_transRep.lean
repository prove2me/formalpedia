-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.isTestRep_transRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:16.006583+00:00
-- url     : https://prove2.me/submissions/0f8fade9-06f5-45cb-86cd-bdf5bd7414cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_WeilProd_isTest_comp_homeomorph

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (ρ : G →* H) (e : X ≃ₜ Y) (W : H → (Y → ℂ) → Y → ℂ) (hW : IsTestRep W) :
    IsTestRep (transRep ρ e.toEquiv W) := by
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have ht : ∀ f, IsTest f → IsTest (f ∘ e.symm) := fun f hf => isTest_comp_homeomorph e.symm hf
  refine ⟨fun g f hf => isTest_comp_homeomorph e (h1 _ _ (ht f hf)), fun f hf => ?_, fun g h f hf => ?_,
    fun g c f f' hf hf' => ?_⟩
  · funext x
    simp [transRep, map_one, h2 _ (ht f hf)]
  · funext x
    show W (ρ (g * h)) (f ∘ e.symm) (e x) = W (ρ g) ((fun x => W (ρ h) (f ∘ e.symm) (e x)) ∘ e.symm) (e x)
    rw [map_mul, h3 _ _ _ (ht f hf)]
    congr 1
    funext y; simp
  · funext x
    have : (c • f + f') ∘ e.toEquiv.symm = c • (f ∘ e.symm) + f' ∘ e.symm := rfl
    simp only [transRep, this, h4 _ c _ _ (ht f hf) (ht f' hf')]
    rfl
end GlobalTheory.JR.WeilProd
