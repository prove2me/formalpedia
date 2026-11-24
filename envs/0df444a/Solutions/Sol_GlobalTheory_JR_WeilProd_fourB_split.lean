-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.fourB_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:21.866946+00:00
-- url     : https://prove2.me/submissions/75f091ea-8915-44f5-9c4c-08fde4402158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_T_fourB_prod_iterated_alt


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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁]
    [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂]
    [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂]
    (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm →
    ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ),
    Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) →
    (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) →
    ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure →
    μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y,
      fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := GlobalTheory.T.fourB_prod_iterated_alt
end GlobalTheory.JR.WeilProd
