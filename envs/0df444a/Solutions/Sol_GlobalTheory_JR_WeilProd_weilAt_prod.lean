-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.weilAt_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:20.992506+00:00
-- url     : https://prove2.me/submissions/fd70ba84-5d38-4750-a011-df142bd576ef

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
import Theorems.Thm_GlobalTheory_JR_WeilProd_isTestRep_transRep
import Theorems.Thm_GlobalTheory_JR_WeilProd_kerL_split
import Theorems.Thm_GlobalTheory_JR_WeilProd_continuous_kerL
import Theorems.Thm_GlobalTheory_JR_WeilProd_tensor_isTestRep
import Theorems.Thm_GlobalTheory_JR_WeilProd_fourB_split
import Theorems.Thm_GlobalTheory_JR_WeilProd_map_nS
import Theorems.Thm_GlobalTheory_JR_WeilProd_map_mS
import Theorems.Thm_GlobalTheory_JR_WeilProd_map_wS
import Theorems.Thm_GlobalTheory_JR_WeilProd_rel_n
import Theorems.Thm_GlobalTheory_JR_WeilProd_rel_m
import Theorems.Thm_GlobalTheory_JR_WeilProd_rel_w
import Theorems.Thm_GlobalTheory_JR_EtMeas_exists_selfDual_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
    IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  intro F E _ _ _ _ U A A₁ A₂ eK eL hS h₁ h₂ ψ hψ x μ hμ
  have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A; have := EtMeas.finite_L A₁; have := EtMeas.finite_L A₂
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.L
  let f₁ : A.K →+* A₁.K := (RingHom.fst A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let f₂ : A.K →+* A₂.K := (RingHom.snd A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let x₁ : A₁.Kˣ := Units.map (f₁ : A.K →* A₁.K) x
  let x₂ : A₂.Kˣ := Units.map (f₂ : A.K →* A₂.K) x
  obtain ⟨μ₁, hμ₁⟩ := EtMeas.exists_selfDual_L A₁ ψ hψ x₁
  obtain ⟨μ₂, hμ₂⟩ := EtMeas.exists_selfDual_L A₂ ψ hψ x₂
  obtain ⟨γ₁, W₁, hW₁⟩ := h₁ ψ hψ x₁ μ₁ hμ₁
  obtain ⟨γ₂, W₂, hW₂⟩ := h₂ ψ hψ x₂ μ₂ hμ₂
  have hc₁ : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc₂ : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let eH : A.L ≃ₜ A₁.L × A₂.L := ⟨eL.toEquiv, hc₁, hc₂⟩
  obtain ⟨c, hc0, hc⟩ := fourB_split eL.toRingEquiv.toAddEquiv hc₁ hc₂ (A.kerL ψ x) (A₁.kerL ψ x₁)
    (A₂.kerL ψ x₂) (continuous_kerL A₁ ψ hψ _) (continuous_kerL A₂ ψ hψ _)
    (fun y' y => kerL_split A A₁ A₂ eK eL hS ψ x y' y) μ μ₁ μ₂ hμ.1 hμ₁.1 hμ₂.1
  let ρ : SpecialLinearGroup (Fin 2) A.K →* SpecialLinearGroup (Fin 2) A₁.K × SpecialLinearGroup (Fin 2) A₂.K :=
    (SpecialLinearGroup.map f₁).prod (SpecialLinearGroup.map f₂)
  obtain ⟨hT, hfib⟩ := tensor_isTestRep W₁ W₂ hW₁.1 hW₂.1
  refine ⟨γ₁ * γ₂ / c, transRep ρ eH.toEquiv (tensorRep W₁ W₂), isTestRep_transRep ρ eH _ hT, fun φ hφ => ?_⟩
  have hf : IsTest (φ ∘ eH.symm) := isTest_comp_homeomorph eH.symm hφ
  obtain ⟨hf1, hf2⟩ := hfib _ hf
  have hy : ∀ y, eH.symm (eL y) = y := fun y => eL.symm_apply_apply y
  have hx₁ : ((x₁ : A₁.Kˣ) : A₁.K) = (eK x).1 := rfl
  have hx₂ : ((x₂ : A₂.Kˣ) : A₂.K) = (eK x).2 := rfl
  refine ⟨fun z y => ?_, fun s y => ?_, fun y => ?_⟩
  · show tensorRep W₁ W₂ (ρ (nS z)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (nS z) = (nS (eK z).1, nS (eK z).2) := Prod.ext (map_nS f₁ z) (map_nS f₂ z)
    rw [hρ, rel_n A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (mS s)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (mS s) = (mS (Units.map (f₁ : A.K →* A₁.K) s), mS (Units.map (f₂ : A.K →* A₂.K) s)) :=
      Prod.ext (map_mS f₁ s) (map_mS f₂ s)
    rw [hρ, rel_m A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2 s _ _ rfl rfl]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (wS A.K)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (wS A.K) = (wS A₁.K, wS A₂.K) := Prod.ext (map_wS f₁) (map_wS f₂)
    rw [hρ, rel_w A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2, hc φ hφ y]
    simp only [Function.comp]
    field_simp
    rfl
end GlobalTheory.JR.WeilProd
