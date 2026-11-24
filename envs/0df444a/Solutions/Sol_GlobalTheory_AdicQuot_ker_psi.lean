-- Prove2me | solution 1 for GlobalTheory.AdicQuot.ker_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:27.771241+00:00
-- url     : https://prove2.me/submissions/14b2a082-00a2-4aa5-997d-0e460f20327a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
import Theorems.Thm_P2M_GlobalTheory_AdicQuot_eval__psi_3e690848319d
import Theorems.Thm_GlobalTheory_AdicQuot_map_val_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)
namespace GlobalTheory.AdicQuot
theorem _root_.solution [IsNoetherianRing A] :
    RingHom.ker (psi J q) = q.map (algebraMap A (AdicCompletion J A)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Submodule.mkQ q) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff J q s n 0).mpr (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := q.mkQ)
      Subtype.val_injective (LinearMap.exact_subtype_mkQ q) (Submodule.mkQ_surjective q)) x).mp hz
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
    rw [Ideal.mem_comap, RingHom.mem_ker]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_psi, _root_.map_zero, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, _root_.map_zero]
end GlobalTheory.AdicQuot
