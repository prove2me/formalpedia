-- Prove2me | solution 1 for IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e288b12d-05e8-57d1-b629-45ae611523fb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one

set_option autoImplicit false
set_option maxHeartbeats 800000

open IsLocalRing in
theorem solution
    (A : Type*) [CommRing A] [IsRegularLocalRing A] (h : ringKrullDim A ≤ 1) :
    IsDomain A ∧ IsIntegrallyClosed A := by
  classical
  have hreg : (Submodule.spanFinrank (maximalIdeal A) : WithBot ℕ∞) = ringKrullDim A :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd1 : Submodule.spanFinrank (maximalIdeal A) ≤ 1 := by
    have h' : (Submodule.spanFinrank (maximalIdeal A) : WithBot ℕ∞) ≤ 1 := hreg ▸ h
    exact_mod_cast h'
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd1 with h0 | h1
  ·
    have hbot : maximalIdeal A = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 h0
    have hfield : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot
    letI := hfield.toField
    exact ⟨inferInstance, inferInstance⟩
  ·
    obtain ⟨s, hscard, hsspan⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal A))
    rw [h1] at hscard
    obtain ⟨π, rfl⟩ := Finset.card_eq_one.1 hscard
    have hmax : maximalIdeal A = Ideal.span {π} := by
      rw [← hsspan, Finset.coe_singleton]
    have hht : (maximalIdeal A).height = 1 := by
      have h2 := hreg.trans (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).symm
      rw [h1] at h2
      exact_mod_cast h2.symm

    have hnotmin : maximalIdeal A ∉ minimalPrimes A := fun hmin => by
      have h0 := (Ideal.height_eq_zero_iff (I := maximalIdeal A)).2 hmin
      rw [hht] at h0
      exact one_ne_zero h0
    obtain ⟨P, hPmin, hP𝔪⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ maximalIdeal A)
    haveI hP : P.IsPrime := hPmin.1.1
    have hPne : P ≠ maximalIdeal A := fun h => hnotmin (h ▸ hPmin)
    have hπP : π ∉ P := fun hπ => hPne (le_antisymm hP𝔪 (by
      rw [hmax, Ideal.span_singleton_le_iff_mem]
      exact hπ))
    have hPle : P ≤ maximalIdeal A • P := by
      intro x hx
      have hx𝔪 : x ∈ Ideal.span {π} := hmax ▸ hP𝔪 hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx𝔪
      have hy : y ∈ P := ((hP.mem_or_mem (by simpa [mul_comm] using hx)).resolve_right hπP)
      rw [mul_comm]
      exact Submodule.smul_mem_smul (hmax ▸ Ideal.mem_span_singleton_self π) hy
    have hPbot : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) P
      (IsNoetherian.noetherian _) hPle (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    haveI : (⊥ : Ideal A).IsPrime := hPbot ▸ hP
    haveI : IsDomain A := Function.Injective.isDomain (RingEquiv.quotientBot A).symm.toRingHom
      (RingEquiv.quotientBot A).symm.injective

    have hnf : ¬ IsField A := fun hf => by
      have hb := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hf
      rw [hb, Submodule.spanFinrank_bot] at h1
      exact zero_ne_one h1
    have hprinc : (maximalIdeal A).IsPrincipal := ⟨⟨π, hmax⟩⟩
    haveI : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 hprinc
    exact ⟨inferInstance, inferInstance⟩

end S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one
end P2MW
export P2MW.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one (solution)
