-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:37.330407+00:00
-- url     : https://prove2.me/submissions/d9147091-e5fc-442c-8220-cd473345cb16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A B L : Type*} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A B] [Algebra A L] [Algebra.Smooth A B] [hL : IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by
  obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp hL
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx ↦ ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := A) hinj
  · obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := A) (S := B) (B := L)).2 ⟨x, hx⟩
    have hy' : Algebra.TensorProduct.map (.id B B) (integralClosure A L).val y = x :=
      congrArg Subtype.val hy
    subst hy'
    clear hx hy
    induction y with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | tmul b y =>
      obtain ⟨a, ha⟩ := hcl y.2
      refine ⟨a • b, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply,
        Subalgebra.coe_val, ← ha, Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul]
      rfl
end GlobalTheory
