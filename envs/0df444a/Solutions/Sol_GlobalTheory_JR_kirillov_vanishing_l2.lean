-- Prove2me | solution 1 for GlobalTheory.JR.kirillov_vanishing_l2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:25.770459+00:00
-- url     : https://prove2.me/submissions/1b9a1deb-6f8a-4ac3-83b7-21b2e82f43ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCellStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimit
import Theorems.Thm_GlobalTheory_JR_LTwoLemma_u_locallyConstant
import Theorems.Thm_GlobalTheory_JR_LTwoLemma_weyl_unipotent_l2_finite
import Theorems.Thm_GlobalTheory_T_eq_zero_of_truncatedFourier_tendsto_zero_etale
import Theorems.Thm_GlobalTheory_T_unimodularHeight_sq_lintegral_lt_top
import Theorems.Thm_GlobalTheory_T_whittakerFunctional_weyl_vanish_of_weylUnipotent_zero
import Theorems.Thm_GlobalTheory_T_whittaker_bound_big_cell


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.JR.LTwoLemma
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd Ψ hI hlim
  have hμ : μK.IsAddHaarMeasure := hsd.1
  have hu : (fun z => Ψ (wS A.K * nS z)) = 0 :=
    GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale F E A ψ hψ μK hsd _ (u_locallyConstant A Ψ hI) (weyl_unipotent_l2_finite GlobalTheory.T.whittaker_bound_big_cell GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top A μK hμ Ψ hI) hlim
  have h1 : ∀ z, Ψ (wS A.K * nS z) = 0 := fun z => congrFun hu z
  exact ⟨h1, GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero F E A ψ μK hμ Ψ hI h1⟩
end GlobalTheory.JR
