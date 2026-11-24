-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.mk0_eq_of_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:26:25.697804+00:00
-- url     : https://prove2.me/submissions/f6610a79-37bf-4c62-9328-dd814a8b79f5

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
theorem _root_.solution (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰) (a : F) (ha : a ≠ 0)
    (J : (Ideal (𝓞 F))⁰) (hJ : ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞 := by
  have hu : FractionalIdeal.mk0 F J = toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha) * FractionalIdeal.mk0 F D * 𝔞 := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, Units.val_mk0]
    exact hJ
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha)) = 1 :=
    ClassGroup.mk_eq_one_iff.2 ⟨⟨a, by rw [coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩⟩
  rw [← ClassGroup.mk_mk0 F, hu, map_mul, map_mul, hp, one_mul, ClassGroup.mk_mk0]
end GlobalTheory.EisConstTerm
