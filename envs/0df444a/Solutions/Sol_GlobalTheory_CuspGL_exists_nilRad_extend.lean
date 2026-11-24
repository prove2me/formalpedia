-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_nilRad_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:08.836402+00:00
-- url     : https://prove2.me/submissions/16499c11-ac0e-4414-9eaf-3e00912b09b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspac
import Theorems.Thm_GlobalTheory_CuspGL_exists_comp_eq_of_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (A W : Submodule F V) (h' : Module.End F W) (hh : h' ∈ nilRad (A.comap W.subtype)) :
    ∃ L : Module.End F V, L ∈ nilRad A ∧ ∀ x : W, L x = h' x := by
  obtain ⟨k, hk⟩ := exists_comp_eq_of_ker_le (A.mkQ ∘ₗ W.subtype)
    (LinearMap.codRestrict A (W.subtype ∘ₗ h') (fun x => hh.1 x)) (by
      intro x hx
      have hx' : (x : V) ∈ A := by simpa using hx
      have := hh.2 x hx'
      rw [LinearMap.mem_ker]
      ext
      simp [this])
  refine ⟨A.subtype ∘ₗ k ∘ₗ A.mkQ, ⟨fun x => by simp, fun x hx => ?_⟩, fun x => ?_⟩
  · have : A.mkQ x = 0 := by simpa using hx
    simp only [LinearMap.comp_apply, this, map_zero]
  · have := congrArg Subtype.val (hk x)
    simpa using this
end GlobalTheory.CuspGL
