-- Prove2me | solution 1 for GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:19.988443+00:00
-- url     : https://prove2.me/submissions/39a5b5d0-4676-484d-a002-90ee750f019c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolutionStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_exists_aeval_eq_of_separable


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | exact GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | (intros; apply GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable <;> assumption)
end _root_.GlobalTheory.T
