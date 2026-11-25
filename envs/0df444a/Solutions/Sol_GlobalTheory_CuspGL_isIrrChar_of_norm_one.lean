-- Prove2me | solution 1 for GlobalTheory.CuspGL.isIrrChar_of_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:19.739478+00:00
-- url     : https://prove2.me/submissions/f3946d5a-94b5-4de1-9196-f2476ff689e3

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrrCharEqOneOfSubsingleton
import Theorems.Thm_GlobalTheory_T_irreducible_of_virtualCharacter_norm_one
import Theorems.Thm_GlobalTheory_T_matrixTrace_iff_isCharacterOverSubfield_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {G : Type} [Group G] [Fintype G] (χ : G → ℂ)
    (h : CuspElliptic.IsIrrChar χ) : GlobalTheory.BI.IsIrrChar ℂ ℂ χ := by
  have hc : GlobalTheory.BI.IsChar ℂ ℂ χ := (GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex G χ).1 h.1
  have hv : χ ∈ GlobalTheory.BI.Virt ℂ ℂ G := AddSubgroup.subset_closure hc
  have hs : ∑ᶠ g, χ g * star (χ g) = (Nat.card G : ℂ) := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]; exact h.2
  exact ((GlobalTheory.T.irreducible_of_virtualCharacter_norm_one G χ hv hs).2 hc).1
end GlobalTheory.CuspGL
