-- Prove2me | solution 1 for GlobalTheory.HeckeTwoConst.exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:45.602032+00:00
-- url     : https://prove2.me/submissions/02b4878c-703b-45d2-93e9-97c7a0f275d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne

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
theorem _root_.solution (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1)
    (a : NZ M) : ∃ J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N},
      ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * N := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * (N : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
    rw [← hM]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 a.2.1) _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 a.2.2
  have hI0 : I ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hs N.ne_zero (by rw [← hI]; simp)
  refine ⟨⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩, hI⟩
  have e : FractionalIdeal.mk0 F ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ = Units.mk0 _ hs * N := by
    ext1
    rw [FractionalIdeal.coe_mk0]
    exact hI
  rw [← ClassGroup.mk_mk0 F, e, map_mul, ClassGroup.mk_eq_one_iff.2, one_mul]
  rw [FractionalIdeal.isPrincipal_iff]
  exact ⟨a.1, rfl⟩
end GlobalTheory.HeckeTwoConst
