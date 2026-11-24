-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_linearEquiv_mem_iff_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:59.292096+00:00
-- url     : https://prove2.me/submissions/8adba984-f205-4c60-81c2-78ef98713e31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadical

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
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B : Submodule F V) (h : Module.finrank F A = Module.finrank F B) :
    ∃ e : V ≃ₗ[F] V, ∀ x, e x ∈ B ↔ x ∈ A := by
  obtain ⟨A', hA⟩ := A.exists_isCompl
  obtain ⟨B', hB⟩ := B.exists_isCompl
  have h' : Module.finrank F A' = Module.finrank F B' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hA
    have h2 := Submodule.finrank_add_eq_of_isCompl hB
    omega
  let e1 := LinearEquiv.ofFinrankEq A B h
  let e2 := LinearEquiv.ofFinrankEq A' B' h'
  refine ⟨(Submodule.prodEquivOfIsCompl A A' hA).symm ≪≫ₗ (e1.prodCongr e2) ≪≫ₗ
    Submodule.prodEquivOfIsCompl B B' hB, fun x => ?_⟩
  obtain ⟨⟨a, a'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A A' hA).surjective x
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
  rw [B.add_mem_iff_right (e1 a).2, A.add_mem_iff_right a.2,
    Submodule.mem_left_iff_eq_zero_of_disjoint hB.disjoint,
    Submodule.mem_left_iff_eq_zero_of_disjoint hA.disjoint]
  simp
end GlobalTheory.CuspGL
