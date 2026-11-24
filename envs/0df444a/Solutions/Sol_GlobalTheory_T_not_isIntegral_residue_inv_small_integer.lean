-- Prove2me | solution 1 for GlobalTheory.T.not_isIntegral_residue_inv_small_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:41.94449+00:00
-- url     : https://prove2.me/submissions/d0252da0-dd44-46bb-a215-29f65c28396a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsIntegralResidueInvSmallInteger
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsIntegralResidueInvSmallIntegerStatement
import Theorems.Thm_GlobalTheory_NotIntegral_inv_small_not_integral


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  first | exact @GlobalTheory.NotIntegral.inv_small_not_integral | exact GlobalTheory.NotIntegral.inv_small_not_integral | (intros; apply GlobalTheory.NotIntegral.inv_small_not_integral <;> assumption)
end _root_.GlobalTheory.T
