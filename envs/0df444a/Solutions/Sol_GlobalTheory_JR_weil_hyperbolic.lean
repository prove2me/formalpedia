-- Prove2me | solution 1 for GlobalTheory.JR.weil_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:49.922431+00:00
-- url     : https://prove2.me/submissions/5b378b13-74d5-4f01-8057-213cdbf3ee79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualHaarHyperbolicKernelPsiKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIdempotentStarEqOneSubOfNotIsFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentCoordinatesStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportIdempotentCoordinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportHyperbolicOperatiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierScaleEqTorusActionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureEtaleHermitianEqCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicWeylActionEqFourierEtaleLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierLinearOnTestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepresentationHyperbolicSplit
import Theorems.Thm_GlobalTheory_JR_weilHyp_rg
import Theorems.Thm_GlobalTheory_JR_weilHyp_nS
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_exists_idempotent_star_eq_one_sub_of_not_isField
import Theorems.Thm_GlobalTheory_T_exists_selfDual_haar_hyperbolicKernelPsiK
import Theorems.Thm_GlobalTheory_T_hyperbolicPartialFourier_linear_on_test
import Theorems.Thm_GlobalTheory_T_hyperbolicPartialFourier_scale_eq_torusAction
import Theorems.Thm_GlobalTheory_T_hyperbolicPartialFourier_twice_eq_reflection
import Theorems.Thm_GlobalTheory_T_hyperbolicWeylAction_eq_fourierEtaleL
import Theorems.Thm_GlobalTheory_T_idempotentCoordinates_structure
import Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_hyperbolic_operations
import Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_idempotentCoordinates_iff
import Theorems.Thm_GlobalTheory_T_isLocallyConstant_etaleTraceAddChar_hermitianKernel
import Theorems.Thm_GlobalTheory_T_partialFourier_psiK_preserves_testFunctions
import Theorems.Thm_GlobalTheory_T_selfDualMeasure_etaleHermitian_eq_coords


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  intro F E _ _ _ _ _ A ψ hψ hK hL x μ hμ
  obtain ⟨e, he, hse⟩ := GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField F E A hK hL
  obtain ⟨hci, hcc, hN, hker, hsm, hunit⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK F E A ψ hψ x
  have hνH : ν.IsAddHaarMeasure := hν.1
  have hT := GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hνH
  have hDD := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ (x : A.K) ν hν
  obtain ⟨hTcc, hTci⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e hci hcc
  obtain ⟨hTrg, hTneg, hTsc, hTmul, hTlin⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations F E A
  obtain ⟨hpsi, hkerlc⟩ := GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ
  obtain ⟨hrg1, hrgm⟩ := weilHyp_rg F E A
  have hlin := GlobalTheory.T.hyperbolicPartialFourier_linear_on_test F E A ψ hψ (x : A.K) ν hνH
  set P := Hyp.pt A ν ψ (x : A.K) with hP
  have h4 : ∀ Φ, IsTest Φ → P (P (P (P Φ))) = Φ := by
    intro Φ hΦ
    rw [hDD Φ hΦ, hDD _ (hTneg Φ hΦ)]
    funext p
    simp
  have hW : ∀ g φ, Hyp.wHyp A e ν ψ x g φ = fun y => P (P (P (Hyp.rg A g (P (fun p => φ (Hyp.cc A e p)))))) (Hyp.ci A e y) :=
    fun _ _ => rfl

  have hkey : ∀ g φ (Φ' : A.K × A.K → ℂ), IsTest Φ' → Hyp.rg A g (P (fun p => φ (Hyp.cc A e p))) = P Φ' →
      Hyp.wHyp A e ν ψ x g φ = fun y => Φ' (Hyp.ci A e y) := by
    intro g φ Φ' hΦ' h
    rw [hW, h, h4 Φ' hΦ']
  have hetaK : ∀ s : A.Kˣ, A.etaK s = 1 := by
    intro s
    have h1 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.1 (Hyp.cc A e ((s : A.K), 1)) (hunit s)
    rwa [hN, mul_one] at h1
  refine ⟨Hyp.wHyp A e ν ψ x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g φ hφ
    rw [hW]
    exact hTci _ (hT _ (hT _ (hT _ (hTrg g _ (hT _ (hTcc φ hφ))))))
  · intro φ hφ
    rw [hW, hrg1, h4 _ (hTcc φ hφ)]
    funext y
    show φ (Hyp.cc A e (Hyp.ci A e y)) = φ y
    rw [hcc]
  · intro g h φ hφ
    have hin : (fun p => Hyp.wHyp A e ν ψ x h φ (Hyp.cc A e p)) = P (P (P (Hyp.rg A h (P (fun p => φ (Hyp.cc A e p)))))) := by
      funext p
      rw [hW]
      simp only [hci]
    rw [hW (g * h) φ, hW g (Hyp.wHyp A e ν ψ x h φ), hin, h4 _ (hTrg h _ (hT _ (hTcc φ hφ))), hrgm]
  · intro g c φ φ' hφ hφ'
    have hc1 : (fun p => (c • φ + φ') (Hyp.cc A e p)) = c • (fun p => φ (Hyp.cc A e p)) + (fun p => φ' (Hyp.cc A e p)) := rfl
    have t1 := hTcc φ hφ
    have t2 := hTcc φ' hφ'
    have hrl : ∀ (Φ Φ' : A.K × A.K → ℂ), Hyp.rg A g (c • Φ + Φ') = c • Hyp.rg A g Φ + Hyp.rg A g Φ' := fun _ _ => rfl
    rw [hW, hW, hW, hc1, hlin c _ _ t1 t2, hrl, hlin c _ _ (hTrg g _ (hT _ t1)) (hTrg g _ (hT _ t2)),
      hlin c _ _ (hT _ (hTrg g _ (hT _ t1))) (hT _ (hTrg g _ (hT _ t2))),
      hlin c _ _ (hT _ (hT _ (hTrg g _ (hT _ t1)))) (hT _ (hT _ (hTrg g _ (hT _ t2))))]
    rfl
  · intro φ hφ
    refine ⟨?_, ?_, ?_⟩
    · intro z y
      have hΦ : IsTest (fun p : A.K × A.K => A.psiK ψ (z * (x : A.K) * (p.1 * p.2)) * φ (Hyp.cc A e p)) :=
        hTmul _ _ (hpsi.comp_continuous (by fun_prop)) (hTcc φ hφ)
      rw [hkey (nS z) φ _ hΦ (weilHyp_nS F E A ν ψ (x : A.K) z _).symm]
      simp only
      rw [← hN, hcc]
    · intro s y
      have hΦ : IsTest (fun p : A.K × A.K => (A.absK (s : A.K) : ℂ) * φ (Hyp.cc A e ((s : A.K) * p.1, (s : A.K) * p.2))) :=
        hTmul _ _ (IsLocallyConstant.const _) (hTsc s _ (hTcc φ hφ))
      rw [hkey (mS s) φ _ hΦ (GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction F E A ν hνH ψ (x : A.K) s (fun p => φ (Hyp.cc A e p))).symm]
      simp only
      rw [hetaK, one_mul, ← hsm, hcc]
    · intro y
      rw [one_mul]
      exact GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL F E A ψ (x : A.K) e ν μ hT hDD (fun Φ hΦ => hTrg _ Φ hΦ) hTcc hcc (hker ψ (x : A.K))
        (hkerlc (x : A.K)) (GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords F E A ψ hψ x e he hse ν μ hν hμ) φ hφ y
end GlobalTheory.JR
