-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.exists_spanSingleton_of_mk0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:26:24.141169+00:00
-- url     : https://prove2.me/submissions/5a7e66c8-1065-4877-b1bb-ab92f5acefbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.EisConstTerm
namespace GlobalTheory.EisConstTerm
theorem _root_.solution (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰)
    (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞) :
    ∃ a : F, a ≠ 0 ∧ ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  set u := FractionalIdeal.mk0 F J * (FractionalIdeal.mk0 F D * 𝔞)⁻¹ with hu_def
  have h1 : ClassGroup.mk F u = 1 := by
    rw [hu_def, map_mul, map_inv, map_mul, ClassGroup.mk_mk0, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hu : (u : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((u : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
    rw [FractionalIdeal.coe_spanSingleton]
    exact hx
  have hx0 : x ≠ 0 := by
    intro h; apply Units.ne_zero u; rw [hu, h, FractionalIdeal.spanSingleton_zero]
  refine ⟨x, hx0, ?_⟩
  have e : FractionalIdeal.mk0 F J = u * (FractionalIdeal.mk0 F D * 𝔞) := by
    rw [hu_def, inv_mul_cancel_right]
  have e' := congrArg Units.val e
  simp only [Units.val_mul, FractionalIdeal.coe_mk0] at e'
  rw [e', hu, mul_assoc]
end GlobalTheory.EisConstTerm
