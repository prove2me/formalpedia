-- Prove2me | solution 1 for GlobalTheory.ParabVirt.map_eq_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:53.713032+00:00
-- url     : https://prove2.me/submissions/c6049993-e63f-4035-b155-258bd7dc3bb8

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
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
private theorem lin_mul_toLinearMap (x y : GL (Fin n) F) :
    (_root_.GlobalTheory.ParabVirt.lin (x * y)).toLinearMap =
      (_root_.GlobalTheory.ParabVirt.lin x).toLinearMap ∘ₗ
        (_root_.GlobalTheory.ParabVirt.lin y).toLinearMap :=
  LinearMap.ext fun v => _root_.GlobalTheory.ParabVirt.lin_mul x y v
end GlobalTheory.ParabVirt
end
end

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
    (s t : GL (Fin n) F) :
    W.map (_root_.GlobalTheory.ParabVirt.lin s).toLinearMap =
        W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap ↔
      s⁻¹ * t ∈ _root_.GlobalTheory.ParabVirt.stab W := by
  constructor
  · intro h v hv
    rw [← _root_.GlobalTheory.ParabVirt.lin_apply, _root_.GlobalTheory.ParabVirt.lin_mul,
      _root_.GlobalTheory.ParabVirt.lin_inv]
    have hmem : _root_.GlobalTheory.ParabVirt.lin t v ∈
        W.map (_root_.GlobalTheory.ParabVirt.lin s).toLinearMap := h ▸ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hw'⟩ := hmem
    simpa [← hw'] using hw
  · intro h
    have h' : ∀ v ∈ W, _root_.GlobalTheory.ParabVirt.lin (s⁻¹ * t) v ∈ W := h
    conv_rhs => rw [show t = s * (s⁻¹ * t) by group]
    rw [lin_mul_toLinearMap, Submodule.map_comp,
      _root_.GlobalTheory.ParabVirt.map_eq_of_stable _ W h']
end _root_.GlobalTheory.ParabVirt
end GlobalTheory.ParabVirt
