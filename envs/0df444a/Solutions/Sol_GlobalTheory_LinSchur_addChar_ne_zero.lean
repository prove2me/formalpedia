-- Prove2me | solution 1 for GlobalTheory.LinSchur.addChar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:08.358533+00:00
-- url     : https://prove2.me/submissions/5004c5a6-ff1c-464f-b369-56bd4d9bebe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenSubgroupPeriodicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetEqSumAddCosetIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LinSchur
namespace GlobalTheory.LinSchur
theorem _root_.solution {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have e := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e
end GlobalTheory.LinSchur
