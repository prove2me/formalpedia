-- Prove2me | solution 1 for GlobalTheory.HL.invVol_conj_of_invVol_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:19.117173+00:00
-- url     : https://prove2.me/submissions/a55a05d8-fb02-4bd6-8212-983cecbf4cd5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InfStabilizerSmulEqConj
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by
  have e : ∀ A B : Subgroup G,
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have hpos : 0 < invVol K (MulAut.conj g • A) := by
    rw [h]; exact (invVol_mul_pos_le_conj K A A hA hA' hA hA').2.1
  have hAB : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hA' hB
  have hBA : B.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hB' hA
  have c1 : K.relIndex (MulAut.conj g • A) ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c2 : (MulAut.conj g • A).relIndex K ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c3 : K.relIndex (MulAut.conj g • B) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans c1 (by rw [e]; exact hAB)
  have c4 : (MulAut.conj g • B).relIndex K ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (by rw [e]; exact hBA) c2
  rw [(invVol_mul_pos_le_conj K _ _ c1 c2 c3 c4).1, (invVol_mul_pos_le_conj K A B hA hA' hB hB').1, h]
  congr 1
  rw [invVol, invVol, e, e]
end GlobalTheory.HL
