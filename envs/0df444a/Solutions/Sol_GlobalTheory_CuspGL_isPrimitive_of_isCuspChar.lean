-- Prove2me | solution 1 for GlobalTheory.CuspGL.isPrimitive_of_isCuspChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:29:15.074196+00:00
-- url     : https://prove2.me/submissions/1bbe1e95-e0a5-4b42-8506-acb6da61dc90

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrrCharEqOneOfSubsingleton
import Theorems.Thm_GlobalTheory_T_isPrimitive_extendZero_of_sum_unipotentRadical
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
theorem _root_.solution {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (χ : GL (Fin d) F → ℂ) (h : CuspElliptic.IsCuspChar χ) : IsPrimitive (extZero χ) := by
  refine GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F d χ ((GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex _ χ).1 h.1.1) fun a ha had => ?_
  have h0 := h.2 a ha had
  change ∑ᶠ u ∈ (CuspElliptic.unipBlock d a : Set (GL (Fin d) F)), χ u = 0
  rw [finsum_mem_def, finsum_eq_sum_of_fintype, ← h0]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ (CuspElliptic.unipBlock d a : Set (GL (Fin d) F))
  · simp [hu]
  · simp [hu]
end GlobalTheory.CuspGL
