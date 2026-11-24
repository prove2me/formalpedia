-- Prove2me | solution 1 for GlobalTheory.laurent_point_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:40.456045+00:00
-- url     : https://prove2.me/submissions/5f16ffe5-1b4b-4076-b284-3d24996067d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_evalAt_single
import Theorems.Thm_GlobalTheory_LaurentConst_hom_ext
import Theorems.Thm_GlobalTheory_LaurentConst_evalAt_const
import Theorems.Thm_GlobalTheory_LaurentConst_evalAt_var
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_zero
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_one
import Theorems.Thm_GlobalTheory_LaurentConst_ext_of_forall_quotient
import Theorems.Thm_GlobalTheory_LaurentConst_specMap_comp
import Theorems.Thm_GlobalTheory_LaurentConst_scale_comp_eq
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LaurentConst
namespace _root_.GlobalTheory
theorem _root_.solution {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsProper B.hom]
    (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S)
    (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ B.left)
    (hf : f ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s) :
    ∃ k : Spec (CommRingCat.of L) ⟶ B.left,
      f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k := by
  refine ⟨Spec.map (CommRingCat.ofHom (evalAt (RingHom.id L) 1)) ≫ f, ?_⟩
  let I : Ideal (AddMonoidAlgebra L ℤ) := Ideal.span {(var L : AddMonoidAlgebra L ℤ) - 1}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 := (Ideal.span_singleton_eq_top.1 h).map (evalAt (RingHom.id L) 1)
    rw [map_sub, map_one, evalAt_var] at h1
    simp at h1
  have : IsNoetherianRing (AddMonoidAlgebra L ℤ) :=
    Algebra.FiniteType.isNoetherianRing L _
  refine ext_of_forall_quotient B.hom ?_ (fun n ↦ I ^ n) (Ideal.iInf_pow_eq_bot_of_isDomain I hI)
    fun n ↦ ?_
  · simp only [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ by simp only [RingHom.comp_apply, evalAt_const, RingHom.id_apply]
  · let ϖ := Ideal.Quotient.mk (I ^ n)
    let r : L →+* _ := ϖ.comp (algebraMap L _)
    let t := Units.map ϖ.toMonoidHom (var L)
    have ht : IsNilpotent ((t : _ ⧸ I ^ n) - 1) := ⟨n, by
      change (ϖ (var L) - 1) ^ n = 0
      rw [← map_one ϖ, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
    have h := congrArg (Spec.map (CommRingCat.ofHom (evalAt (RingHom.id _) 1)) ≫ ·)
      (scale_comp_eq s f hf r t ht)
    simp only [specMap_comp] at h ⊢
    convert h using 4 <;> refine LaurentConst.hom_ext (fun c ↦ ?_) ?_ <;>
      simp only [RingHom.comp_apply, scale_single_zero, scale_single_one, evalAt_single, one_zpow,
        Units.val_one, _root_.mul_one, RingHom.id_apply, map_one] <;> rfl
end _root_.GlobalTheory
end GlobalTheory.LaurentConst
