-- Prove2me | solution 1 for GlobalTheory.CuspGL.extZero_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:42.033993+00:00
-- url     : https://prove2.me/submissions/322ed3bf-44ad-4d5d-96bf-b09f1c147808

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
import Theorems.Thm_GlobalTheory_CuspGL_extZero_toLin
import Theorems.Thm_GlobalTheory_CuspGL_extZero_of_not_isUnit
import Theorems.Thm_GlobalTheory_CuspGL_ipGL_eq_finsum_GL
import Theorems.Thm_GlobalTheory_CuspGL_isClassFn_extZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {d : ℕ}
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  intro F _ _ d χ
  exact ⟨fun x => extZero_toLin χ x, fun g hg => extZero_of_not_isUnit χ g hg,
    fun φ φ' => ipGL_eq_finsum_GL φ φ', fun h => isClassFn_extZero χ h⟩
end GlobalTheory.CuspGL
