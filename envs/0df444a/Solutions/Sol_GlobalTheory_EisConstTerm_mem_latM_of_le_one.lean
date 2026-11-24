-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.mem_latM_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:26:24.839343+00:00
-- url     : https://prove2.me/submissions/ff285828-a996-4aa6-b890-f96d3ce607e4

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
theorem _root_.solution (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F)
    (ha : FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) : a ∈ latM 𝔞 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ a
      = FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * latM 𝔞 := by
        rw [latM, show ∀ X : FractionalIdeal (𝓞 F)⁰ F, X * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (cD⁻¹ * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) =
          X * (cD * cD⁻¹) * ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) from fun X => by ring,
          mul_inv_cancel₀ hcD, Units.mul_inv, mul_one, mul_one]
    _ ≤ 1 * latM 𝔞 := by gcongr
    _ = latM 𝔞 := one_mul _
end GlobalTheory.EisConstTerm
