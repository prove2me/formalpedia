-- Prove2me | solution 1 for GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:18.859164+00:00
-- url     : https://prove2.me/submissions/ba4e3d28-8185-4a15-87d1-61ba92c1a98e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar
import Theorems.Thm_GlobalTheory_StandardAdditiveCharacter_exists_stdAddChar_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StandardAdditiveCharacter
namespace GlobalTheory.StandardAdditiveCharacter
theorem _root_.solution (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun (φ : Module.Dual (ZMod n) A) ↦
      AddChar.compAddMonoidHom ZMod.stdAddChar (LinearMap.toAddMonoidHom φ) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro a
    have h' := congr_arg (fun χ : AddChar A ℂ => χ a) h
    simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h'
    exact ZMod.injective_stdAddChar h'
  · intro ψ
    have hroot : ∀ a : A, (ψ a) ^ n = 1 := by
      intro a
      rw [← AddChar.map_nsmul_eq_pow]
      have h0 : n • a = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
      rw [h0, AddChar.map_zero_eq_one]
    choose j hj using fun a => exists_stdAddChar_eq n (ψ a) (hroot a)
    let F : A →+ ZMod n :=
      { toFun := j
        map_zero' := ZMod.injective_stdAddChar (by simp [hj])
        map_add' := fun a b => ZMod.injective_stdAddChar (by simp only [AddChar.map_add_eq_mul, hj]) }
    refine ⟨F.toZModLinearMap n, ?_⟩
    ext a
    simp [F, hj]
end GlobalTheory.StandardAdditiveCharacter
