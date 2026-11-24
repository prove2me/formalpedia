-- Prove2me | solution 1 for GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:10:51.686269+00:00
-- url     : https://prove2.me/submissions/65f35b94-a161-4ef4-a1ab-13d23b14ad63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_gramDet_eq_norm_mul


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | exact GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | (intros; apply GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul <;> assumption)
end _root_.GlobalTheory.T
