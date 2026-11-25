-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.lam_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:16.87755+00:00
-- url     : https://prove2.me/submissions/7bc510b3-da7a-44aa-b435-f5baff56fb0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeylStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventuallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleOrbitalFourierRankOneTransfer
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_lam_integrand_cont
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.RankOneTransfer
namespace GlobalTheory.JR.RankOneTransfer
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K),
    μK.IsAddHaarMeasure → ∀ (a : A.K) (Φ₁ Φ₂ : SpecialLinearGroup (Fin 2) A.K → ℂ) (r : ℂ), A.InI Φ₁ → A.InI Φ₂ →
    ∀ c : F, c ≠ 0 → A.abelian₂ μK ψ a (fun g => Φ₁ g + r * Φ₂ g) c = A.abelian₂ μK ψ a Φ₁ c + r * A.abelian₂ μK ψ a Φ₂ c := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ a Φ₁ Φ₂ r h₁ h₂ c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hOKo, hOKc, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hKc : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have := (Homeomorph.smulOfNeZero c hc (α := A.K)).isCompact_preimage.2 hOKc
    exact this
  have hKm : MeasurableSet {z : A.K | c • z ∈ A.OK} := (hOKo.preimage hsm).measurableSet
  have i₁ : IntegrableOn (fun z => Φ₁ (wS A.K * nS z) * A.psiK ψ (-(a * z))) {z : A.K | c • z ∈ A.OK} μK :=
    (lam_integrand_cont A ψ hψ a Φ₁ h₁).continuousOn.integrableOn_compact' hKc hKm
  have i₂ : IntegrableOn (fun z => Φ₂ (wS A.K * nS z) * A.psiK ψ (-(a * z))) {z : A.K | c • z ∈ A.OK} μK :=
    (lam_integrand_cont A ψ hψ a Φ₂ h₂).continuousOn.integrableOn_compact' hKc hKm
  simp only [Et.abelian₂]
  rw [← integral_const_mul, ← integral_add i₁ (i₂.const_mul r)]
  congr 1
  funext z
  ring
end GlobalTheory.JR.RankOneTransfer
