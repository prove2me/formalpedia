-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.measure_eq_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:52.141158+00:00
-- url     : https://prove2.me/submissions/10c03960-58f3-42e6-995c-3244747fb3d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentCoordinatesStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportIdempotentCoordinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureEtaleHermitianEqCoords
import Theorems.Thm_GlobalTheory_FourKFub_secondCountableK
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_MeasScale_selfDual_unique
import Theorems.Thm_GlobalTheory_JR_SelfDualUniq_selfDual_unique
import Theorems.Thm_GlobalTheory_T_hyperbolicPartialFourier_twice_eq_reflection
import Theorems.Thm_GlobalTheory_T_idempotentCoordinates_structure
import Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_idempotentCoordinates_iff
import Theorems.Thm_GlobalTheory_T_isLocallyConstant_etaleTraceAddChar_hermitianKernel
import Theorems.Thm_GlobalTheory_T_partialFourier_psiK_preserves_testFunctions


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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  intro F E _ _ _ _ _ A ψ hψ x e he hse ν μ hν hμ h hh
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI := EtMeas.finite_L A
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨h1, h2, -, hker, -⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨htc, htc'⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e h1 h2
  have hlc := (GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ).2 (x : A.K)
  haveI : ν.IsAddHaarMeasure := hν.1
  let C := ccEquiv A e h1 h2
  have hC : (C : A.K × A.K → A.L) = cc A e := rfl
  set μ₀ := Measure.map (cc A e) (ν.prod ν) with hμ₀
  haveI : μ₀.IsAddHaarMeasure := by rw [hμ₀, ← hC]; exact C.isAddHaarMeasure_map _
  have hint : ∀ g : A.L → ℂ, IsTest g → ∫ y, g y ∂μ₀ = ∫ a, ∫ b, g (cc A e (a, b)) ∂ν ∂ν := by
    intro g hg
    have e1 : ∫ y, g y ∂μ₀ = ∫ p, g (cc A e p) ∂(ν.prod ν) := C.toHomeomorph.measurableEmbedding.integral_map g
    rw [e1]
    exact integral_prod _ (((htc g hg).1.continuous).integrable_of_hasCompactSupport (htc g hg).2)
  have hsw : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun q : A.K × A.K => Φ (q.2, q.1)) := fun Φ hΦ =>
    ⟨hΦ.1.comp_continuous continuous_swap, hΦ.2.comp_homeomorph (Homeomorph.prodComm A.K A.K)⟩
  have hpt : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (pt A ν ψ x Φ) := fun Φ hΦ =>
    GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hν.1 Φ hΦ
  have hT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (tt A ν ψ x Φ) := fun Φ hΦ =>
    hpt _ (hsw _ (hpt Φ hΦ))
  have hTT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → tt A ν ψ x (tt A ν ψ x Φ) = fun p => Φ (-p.1, -p.2) := by
    intro Φ hΦ
    have i1 := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ x ν hν _ (hsw _ (hpt Φ hΦ))
    have i2 := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ x ν hν Φ hΦ
    funext p
    show pt A ν ψ x (fun q => pt A ν ψ x (pt A ν ψ x (fun q' => pt A ν ψ x Φ (q'.2, q'.1))) (q.2, q.1)) p = _
    rw [i1]
    show pt A ν ψ x (pt A ν ψ x Φ) (-p.1, p.2) = _
    rw [i2]
  have hA : ∀ f : A.L → ℂ, IsTest f → ∀ p,
      fourB μ₀ (A.kerL ψ x) f (cc A e p) = tt A ν ψ x (fun q => f (cc A e q)) p := by
    intro f hf p
    have ht : IsTest (fun z => f z * A.kerL ψ x z (cc A e p)) := ⟨hf.1.mul (hlc _), hf.2.mul_right⟩
    unfold fourB
    rw [hint _ ht]
    show _ = ∫ a, (∫ b, f (cc A e (a, b)) * kx A ψ x b p.1 ∂ν) * kx A ψ x a p.2 ∂ν
    congr 1; funext a
    rw [← integral_mul_const]
    congr 1; funext b
    rw [hker]; dsimp only; ring
  have hB : ∀ f : A.L → ℂ, IsTest f → IsTest (fourB μ₀ (A.kerL ψ x) f) := by
    intro f hf
    have : fourB μ₀ (A.kerL ψ x) f = fun y => tt A ν ψ x (fun q => f (cc A e q)) (ci A e y) := by
      funext y; have := hA f hf (ci A e y); rwa [h2] at this
    rw [this]; exact htc' _ (hT _ (htc f hf))
  have hsd : SelfDual μ₀ (A.kerL ψ x) := by
    refine ⟨inferInstance, fun f hf y => ?_⟩
    rw [← h2 y, hA _ (hB f hf)]
    have : (fun q => fourB μ₀ (A.kerL ψ x) f (cc A e q)) = tt A ν ψ x (fun q => f (cc A e q)) :=
      funext (hA f hf)
    rw [this, hTT _ (htc f hf)]
    dsimp only
    congr 1
    simp only [cc, map_neg]; ring
  have heq : μ = μ₀ := MeasScale.selfDual_unique hS (A.kerL ψ x) hsd hμ
  rw [heq]; exact hint h hh
end GlobalTheory.JR.Hyp
