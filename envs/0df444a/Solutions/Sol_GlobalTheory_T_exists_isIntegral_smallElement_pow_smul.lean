-- Prove2me | solution 1 for GlobalTheory.T.exists_isIntegral_smallElement_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:38.039675+00:00
-- url     : https://prove2.me/submissions/833eff3a-dd44-4c05-88a7-000e16dc6eff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsIntegralSmallElementPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsIntegralSmallElementPowSmulStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_smul_pow_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A, ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  first | exact @GlobalTheory.UnitLemma.Desc.smul_pow_integral | exact GlobalTheory.UnitLemma.Desc.smul_pow_integral | (intros; apply GlobalTheory.UnitLemma.Desc.smul_pow_integral <;> assumption)
end _root_.GlobalTheory.T
