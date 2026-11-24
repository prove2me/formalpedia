-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:35.883058+00:00
-- url     : https://prove2.me/submissions/9ccb6af4-1c72-4cf8-888d-71cd9fb654a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIffForallMaximalSpectrumResidue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIffForallMaximalSpectrumResidueStatement
import Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_iff_forall_maximalSpectrum


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ x : B.A, IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  first | exact @GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum | exact GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum | (intros; apply GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum <;> assumption)
end _root_.GlobalTheory.T
