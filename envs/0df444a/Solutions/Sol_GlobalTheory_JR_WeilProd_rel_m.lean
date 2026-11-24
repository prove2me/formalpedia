-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.rel_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:42.26686+00:00
-- url     : https://prove2.me/submissions/f846768b-eeb7-467e-b4b3-d6806230ed6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_WeilProd_etaK_split
import Theorems.Thm_GlobalTheory_JR_WeilProd_smul_split
import Theorems.Thm_GlobalTheory_JR_WeilProd_absK_split

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
variable [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
  (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K)
  (W₁ : SpecialLinearGroup (Fin 2) A₁.K → (A₁.L → ℂ) → A₁.L → ℂ)
  (W₂ : SpecialLinearGroup (Fin 2) A₂.K → (A₂.L → ℂ) → A₂.L → ℂ) (γ₁ γ₂ : ℂ) (μ₁ : Measure A₁.L) (μ₂ : Measure A₂.L)
  (hW₁ : A₁.IsWeil ψ (eK x).1 A₁.etaK μ₁ γ₁ W₁) (hW₂ : A₂.IsWeil ψ (eK x).2 A₂.etaK μ₂ γ₂ W₂)
  (f : A₁.L × A₂.L → ℂ) (hf1 : ∀ u, IsTest (fun v => f (u, v)))
  (hf2 : ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y))
include hS hW₁ hW₂ hf1 hf2
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution (s : A.Kˣ) (s₁ : A₁.Kˣ) (s₂ : A₂.Kˣ) (hs₁ : (s₁ : A₁.K) = (eK s).1) (hs₂ : (s₂ : A₂.K) = (eK s).2)
    (y : A.L) :
    tensorRep W₁ W₂ (mS s₁, mS s₂) f (eL y) = A.etaK s * (A.absK s : ℂ) * f (eL ((s : A.K) • y)) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (mS s₂) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.etaK s₂ * (A₂.absK s₂ : ℂ) * f (u, (s₂ : A₂.K) • (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.1 _ _
  have t := hf2 (mS s₂) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.1, smul_split A A₁ A₂ eK eL hS, etaK_split A A₁ A₂ eK s,
    absK_split F E A A₁ A₂ eK s, hs₁, hs₂]
  push_cast
  ring
end GlobalTheory.JR.WeilProd
