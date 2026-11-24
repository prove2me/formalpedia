-- Prove2me | solution 1 for GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:42:35.362328+00:00
-- url     : https://prove2.me/submissions/448555d1-4a7f-452d-9755-5caddb53e9a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Theorems.Thm_GlobalTheory_CuspGL_extZero_spec


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  first | exact @GlobalTheory.CuspGL.extZero_spec | exact GlobalTheory.CuspGL.extZero_spec | (intros; apply GlobalTheory.CuspGL.extZero_spec <;> assumption)
end _root_.GlobalTheory.T
