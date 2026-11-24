-- Prove2me | solution 1 for GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:45.220948+00:00
-- url     : https://prove2.me/submissions/da0b54d8-005e-446c-862c-014e2a6599d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLeStatement
import Theorems.Thm_GlobalTheory_QNorm_index_sqSub_adicCompletion_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  first | exact @GlobalTheory.QNorm.index_sqSub_adicCompletion_le | exact GlobalTheory.QNorm.index_sqSub_adicCompletion_le | (intros; apply GlobalTheory.QNorm.index_sqSub_adicCompletion_le <;> assumption)
end _root_.GlobalTheory.T
