-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_residue_comap_involution_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:34.143295+00:00
-- url     : https://prove2.me/submissions/a0222702-fa7e-4700-b6db-ca81bbe38092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIffStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isIntegral_mk_comap_sigma_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A), IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔ IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | exact GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | (intros; apply GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff <;> assumption)
end _root_.GlobalTheory.T
