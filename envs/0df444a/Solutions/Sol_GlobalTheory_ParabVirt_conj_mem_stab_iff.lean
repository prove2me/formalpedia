-- Prove2me | solution 1 for GlobalTheory.ParabVirt.conj_mem_stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:52.019064+00:00
-- url     : https://prove2.me/submissions/6a05426c-6ce5-42ee-b9eb-7307d59746d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial
variable {F : Type} [Field F] {n : ℕ}
namespace GlobalTheory.ParabVirt
namespace _root_.GlobalTheory.ParabVirt
theorem _root_.solution (W : Submodule F (Fin n → F))
    (x t : GL (Fin n) F) :
    t⁻¹ * x * t ∈ _root_.GlobalTheory.ParabVirt.stab W ↔
      x ∈ _root_.GlobalTheory.ParabVirt.stab (W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap) := by
  change (∀ v ∈ W, _root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) v ∈ W) ↔
    ∀ v ∈ W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap, _root_.GlobalTheory.ParabVirt.lin x v ∈
      W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap
  constructor
  · rintro h _ ⟨w, hw, rfl⟩
    refine ⟨_root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) w, h w hw, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [← _root_.GlobalTheory.ParabVirt.lin_mul, ← _root_.GlobalTheory.ParabVirt.lin_mul,
      show t * (t⁻¹ * x * t) = x * t by group]
  · intro h w hw
    obtain ⟨u, hu, hu'⟩ := h (_root_.GlobalTheory.ParabVirt.lin t w) ⟨w, hw, rfl⟩
    have hwu : _root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) w = u := by
      rw [show t⁻¹ * x * t = t⁻¹ * (x * t) by group, _root_.GlobalTheory.ParabVirt.lin_mul,
        _root_.GlobalTheory.ParabVirt.lin_mul, ← hu', LinearEquiv.coe_coe,
        _root_.GlobalTheory.ParabVirt.lin_inv, LinearEquiv.symm_apply_apply]
    rw [hwu]
    exact hu
end _root_.GlobalTheory.ParabVirt
end GlobalTheory.ParabVirt
