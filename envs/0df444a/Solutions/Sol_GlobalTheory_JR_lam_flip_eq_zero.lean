-- Prove2me | solution 1 for GlobalTheory.JR.lam_flip_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:14.717819+00:00
-- url     : https://prove2.me/submissions/923cfbc1-2172-44b2-bc5d-0eac21204973

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZero
import Theorems.Thm_GlobalTheory_JR_wS_nS_wS_eq_unit
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
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ μK hμ Ψ hΨ h0 a c
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ z ∂μK, IsUnit z := ae_iff.2 hnull
  unfold Et.abelian₂
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  filter_upwards [hae] with z hz
  obtain ⟨u, rfl⟩ := hz
  simp only [Pi.zero_apply]
  rw [wS_nS_wS_eq_unit u, hΨ.2, h0, mul_zero, zero_mul]
end GlobalTheory.JR
