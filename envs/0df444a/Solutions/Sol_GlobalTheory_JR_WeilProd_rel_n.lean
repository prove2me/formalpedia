-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.rel_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:26.102104+00:00
-- url     : https://prove2.me/submissions/93d882bd-8e02-436f-9796-b23e5b9ff79c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_WeilProd_psiK_split

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
theorem _root_.solution (z : A.K) (y : A.L) :
    tensorRep W₁ W₂ (nS (eK z).1, nS (eK z).2) f (eL y) = A.psiK ψ (z * x * A.NL y) * f (eL y) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (nS (eK z).2) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) * f (u, (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).1 _ _
  have t := hf2 (nS (eK z).2) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).1, psiK_split A A₁ A₂ eK eL hS ψ z x y]
  ring
end GlobalTheory.JR.WeilProd
