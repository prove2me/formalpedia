-- Prove2me | solution 1 for GlobalTheory.HeckeTwoConst.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:51.72163+00:00
-- url     : https://prove2.me/submissions/c67a7df6-6f0e-4802-bb83-f3ed8384cc67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne
import Theorems.Thm_GlobalTheory_HeckeTwoConst_exists_ideal

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
open GlobalTheory GlobalTheory.HeckeTwoConst
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoConst
theorem _root_.solution (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1) :
    ∃ e : Quotient (unitRel M) ≃ {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N}, ∀ c,
      (((e c).1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c.out.1 * N := by
  choose f hf using exists_ideal M N hM
  have key : ∀ a b : NZ M, (unitRel M).r a b ↔
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 := by
    intro a b
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine exists_congr fun ε => ?_
    rw [Units.smul_def, Algebra.smul_def]
    exact eq_comm
  refine ⟨Equiv.ofBijective (fun c => f c.out) ⟨?_, ?_⟩, fun c => hf _⟩
  · intro c c' h
    have h1 := hf c.out
    simp only at h
    rw [h, hf] at h1
    have h2 := (key _ _).2 (mul_right_cancel₀ N.ne_zero h1).symm
    rw [← c.out_eq, ← c'.out_eq]
    exact Quotient.sound h2
  · rintro ⟨J, hJ⟩
    have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * N⁻¹) = 1 := by
      rw [map_mul, map_inv, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h1
    obtain ⟨a, ha⟩ := h1
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.1 (ha ▸ Units.ne_zero _)
    have hMN : M = ((N⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hM
    rw [Units.val_mul, FractionalIdeal.coe_mk0, ← hMN] at ha
    have haM : a ∈ M := by
      rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← ha]
      conv_rhs => rw [← one_mul M]
      exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
    refine ⟨Quotient.mk _ ⟨a, haM, ha0⟩, ?_⟩
    have h2 : (unitRel M).r (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out ⟨a, haM, ha0⟩ :=
      Quotient.exact (Quotient.out_eq _)
    have h3 := hf (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out
    rw [(key _ _).1 h2] at h3
    simp only at h3
    rw [← ha, mul_assoc, hM, mul_one] at h3
    exact Subtype.ext (Subtype.ext (FractionalIdeal.coeIdeal_injective h3))
end GlobalTheory.HeckeTwoConst
