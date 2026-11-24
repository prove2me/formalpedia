-- Prove2me | solution 1 for GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:03.604221+00:00
-- url     : https://prove2.me/submissions/fd862fa3-adcd-411e-96c6-f19a8343200f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadical
import Theorems.Thm_GlobalTheory_CuspGL_exists_linearEquiv_mem_iff_of_finrank_eq
import Theorems.Thm_GlobalTheory_CuspGL_finsum_nilRad_extZero_eq_zero
import Theorems.Thm_GlobalTheory_T_exists_standardUnipotentRadical_bijOn_nilradical
import Theorems.Thm_GlobalTheory_T_generalLinearFunctionExtendZeroEnd_properties
import Theorems.Thm_GlobalTheory_isChar_restrict_conj_one


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
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  intro F _ _ d χ hχ hs A hA0 hA1 g hg
  have ha0 : 0 < Module.finrank F A := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hA0 (Submodule.finrank_eq_zero.1 h)
  have ha1 : Module.finrank F A < d := by
    have := Submodule.finrank_lt hA1
    simpa using this
  obtain ⟨B, H, hB, hH, hb⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d _ ha1.le
  have h0 := hs _ ha0 ha1
  rw [← hH] at h0
  obtain ⟨e, he⟩ := exists_linearEquiv_mem_iff_of_finrank_eq A B hB.symm
  have hcl := (GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ).2.2.2 (GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ hχ).2.1
  have key := finsum_nilRad_extZero_eq_zero F d χ hχ B H hb h0 (e.conj g) (fun x hx => by
    rw [LinearEquiv.conj_apply_apply, he]
    apply hg
    rw [← he]
    simpa using hx)
  rw [← key]
  refine finsum_mem_eq_of_bijOn (fun h => e.conj h) ⟨fun h hh => ⟨fun y => ?_, fun y hy => ?_⟩,
    e.conj.injective.injOn, fun h hh => ⟨e.symm.conj h, ⟨fun y => ?_, fun y hy => ?_⟩, by ext y; simp [LinearEquiv.conj_apply_apply]⟩⟩ fun h _ => ?_
  · rw [LinearEquiv.conj_apply_apply, he]
    exact hh.1 _
  · rw [LinearEquiv.conj_apply_apply, hh.2 _ (by rw [← he]; simpa using hy), map_zero]
  · rw [← he, LinearEquiv.conj_apply_apply]
    simpa using hh.1 _
  · rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, hh.2 _ ((he y).2 hy), map_zero]
  · rw [← map_add, hcl]
end GlobalTheory.CuspGL
