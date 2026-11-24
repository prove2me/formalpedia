-- Prove2me | solution 1 for GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:11.586797+00:00
-- url     : https://prove2.me/submissions/89b15dc1-d4c8-49e1-b66e-dcdd23a41db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Theorems.Thm_GlobalTheory_BI_matrixChar_iff_isChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] (χ : G → ℂ), (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔ IsChar ℂ ℂ χ := by
  first | exact @GlobalTheory.BI.matrixChar_iff_isChar | exact GlobalTheory.BI.matrixChar_iff_isChar | (intros; apply GlobalTheory.BI.matrixChar_iff_isChar <;> assumption)
end _root_.GlobalTheory.T
