-- Prove2me | solution 1 for GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:11.67027+00:00
-- url     : https://prove2.me/submissions/e8146dcb-88d4-4600-b71f-56892d8b4b4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
import Theorems.Thm_GlobalTheory_QNorm_index_locSq_le


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.index_locSq_le | exact GlobalTheory.QNorm.index_locSq_le | (intros; apply GlobalTheory.QNorm.index_locSq_le <;> assumption)
end _root_.GlobalTheory.T
