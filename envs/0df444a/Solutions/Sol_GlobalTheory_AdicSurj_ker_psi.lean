-- Prove2me | solution 1 for GlobalTheory.AdicSurj.ker_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:31.541206+00:00
-- url     : https://prove2.me/submissions/8f194d89-47cd-4c7f-bc5d-6c2c5dcda304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicSurj_map_val_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicSurj
open AdicCompletion
variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
namespace GlobalTheory.AdicSurj
theorem _root_.solution [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    RingHom.ker (psi B J) =
      Ideal.map (algebraMap A (AdicCompletion J A)) (LinearMap.ker (Algebra.linearMap A B)) := by
  set q := LinearMap.ker (Algebra.linearMap A B)
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Algebra.linearMap A B) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff B J s n 0).mpr
        (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := Algebra.linearMap A B)
      Subtype.val_injective (LinearMap.exact_subtype_ker_map _) hs) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, psi_algebraMap, AdicCompletion.algebraMap_apply]
    have : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [this, _root_.map_zero]
end GlobalTheory.AdicSurj
