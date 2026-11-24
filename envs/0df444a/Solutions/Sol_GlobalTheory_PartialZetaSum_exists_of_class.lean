-- Prove2me | solution 1 for GlobalTheory.PartialZetaSum.exists_of_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:56.425452+00:00
-- url     : https://prove2.me/submissions/106cca86-fb8c-42f3-a6f3-241159b8c87e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.PartialZetaSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.PartialZetaSum
theorem _root_.solution (𝔟 : Frac F) (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹) :
    ∃ b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), idealOf 𝔟 b = J.1 := by
  have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * 𝔟) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hx' : ((FractionalIdeal.mk0 F J * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    beta_reduce
    rw [FractionalIdeal.coe_spanSingleton]; exact hx
  rw [Units.val_mul, FractionalIdeal.coe_mk0] at hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx'
    exact (mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero J)) (Units.ne_zero 𝔟)) hx'
  have hxm : x ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
    have : FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [← hx']
      calc ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
          ≤ 1 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
        _ = _ := one_mul _
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 this
  let b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := ⟨x, hxm, hx0⟩
  refine ⟨b, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe]
  show FractionalIdeal.spanSingleton (𝓞 F)⁰ x * _ = _
  rw [← hx', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
end GlobalTheory.PartialZetaSum
