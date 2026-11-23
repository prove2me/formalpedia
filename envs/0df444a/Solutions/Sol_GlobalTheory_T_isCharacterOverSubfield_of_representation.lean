-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_of_representation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:56.394867+00:00
-- url     : https://prove2.me/submissions/9a27c8c9-2507-4f0a-90e8-ce2196484467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentationStatement
import Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V), IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧ (ρ.IsIrreducible → IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  first | exact @GlobalTheory.BI.isChar_and_isIrrChar_of_rep | exact GlobalTheory.BI.isChar_and_isIrrChar_of_rep | (intros; apply GlobalTheory.BI.isChar_and_isIrrChar_of_rep <;> assumption)
end _root_.GlobalTheory.T
