-- Prove2me | solution 1 for GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:10.905492+00:00
-- url     : https://prove2.me/submissions/e8296661-ac8b-4156-9bcd-75fef05bc527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPolyStatement
import Theorems.Thm_GlobalTheory_UnitLemma_exists_invAlg_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic → C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  first | exact @GlobalTheory.UnitLemma.exists_invAlg_root | exact GlobalTheory.UnitLemma.exists_invAlg_root | (intros; apply GlobalTheory.UnitLemma.exists_invAlg_root <;> assumption)
end _root_.GlobalTheory.T
