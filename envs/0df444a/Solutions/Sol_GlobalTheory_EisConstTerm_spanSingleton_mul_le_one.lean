-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.spanSingleton_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:26:26.386562+00:00
-- url     : https://prove2.me/submissions/abbf8428-9e8c-4554-8b40-95acada4a510

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
theorem _root_.solution (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (ha : a ∈ latM 𝔞) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have h := FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  calc _ ≤ latM 𝔞 * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by gcongr
    _ = (cD⁻¹ * cD) * (((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * 𝔞) := by rw [latM]; ring
    _ = 1 := by rw [inv_mul_cancel₀ hcD, Units.inv_mul, one_mul]
end GlobalTheory.EisConstTerm
