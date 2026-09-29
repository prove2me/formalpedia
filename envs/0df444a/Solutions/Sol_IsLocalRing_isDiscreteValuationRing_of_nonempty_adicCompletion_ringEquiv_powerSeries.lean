-- Prove2me | solution 1 for IsLocalRing.isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/16b5ae75-bc67-57af-b242-6436445375a7

import Mathlib
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Theorems.Thm_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

universe u v

open IsLocalRing

noncomputable section

namespace COREFSM

section Rh
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

abbrev Rh (R : Type*) [CommRing R] [IsLocalRing R] : Type _ := AdicCompletion (maximalIdeal R) R
abbrev mh (R : Type*) [CommRing R] [IsLocalRing R] : Ideal (Rh R) := (maximalIdeal R).map (algebraMap R (Rh R))

scoped instance : IsAdicComplete (maximalIdeal R) (Rh R) := AdicCompletion.isAdicComplete (IsNoetherian.noetherian _)
scoped instance : IsAdicComplete (mh R) (Rh R) := (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

theorem algebraMap_Rh_apply (r : R) : algebraMap R (Rh R) r = AdicCompletion.of (maximalIdeal R) R r := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem algebraMap_Rh_injective : Function.Injective (algebraMap R (Rh R)) := by
  intro a b hab
  rw [algebraMap_Rh_apply, algebraMap_Rh_apply] at hab
  exact AdicCompletion.of_injective (maximalIdeal R) R hab

theorem exists_sub_algebraMap_mem (n : ℕ) (x : Rh R) :
    ∃ r : R, x - algebraMap R (Rh R) r ∈ ((maximalIdeal R) ^ n • ⊤ : Submodule R (Rh R)) := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal R) R n x)
  refine ⟨r, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _), LinearMap.mem_ker, map_sub,
    algebraMap_Rh_apply, AdicCompletion.eval_of, ← hr, sub_eq_zero]
  rfl

theorem mh_isMaximal : (mh R).IsMaximal := by

  let π : R →+* Rh R ⧸ mh R := (Ideal.Quotient.mk (mh R)).comp (algebraMap R (Rh R))
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem 1 x
    refine ⟨r, ?_⟩
    show Ideal.Quotient.mk (mh R) (algebraMap R (Rh R) r) = Ideal.Quotient.mk (mh R) x
    rw [Ideal.Quotient.eq]
    rw [pow_one, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hr
    have := neg_mem_iff.mpr hr
    rwa [neg_sub] at this
  have hker : RingHom.ker π = maximalIdeal R := by
    ext r
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      IsLocalRing.comap_map_adicCompletion_eq]
  have hfield : IsField (Rh R ⧸ mh R) := by
    let e := RingHom.quotientKerEquivOfSurjective hπs
    have : IsField (R ⧸ RingHom.ker π) := by
      rw [hker, ← Ideal.Quotient.maximal_ideal_iff_isField_quotient]; exact maximalIdeal.isMaximal R
    exact MulEquiv.isField this e.symm.toMulEquiv
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.mpr hfield

scoped instance : IsLocalRing (Rh R) :=
  haveI := mh_isMaximal (R := R)
  isLocalRing_of_isAdicComplete_maximal (mh R)

theorem maximalIdeal_Rh : maximalIdeal (Rh R) = mh R :=
  haveI := mh_isMaximal (R := R)
  (IsLocalRing.eq_maximalIdeal inferInstance).symm

end Rh

end COREFSM
p2m_reactivate "P2MW.S_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries.COREFSM"

open COREFSM in
theorem solution
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type v) [Field k]
    (e : Nonempty (AdicCompletion (maximalIdeal A) A ≃+* PowerSeries k)) :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  classical
  obtain ⟨e⟩ := e

  haveI hRhdom : IsDomain (Rh A) := Function.Injective.isDomain e.toRingHom e.injective
  haveI hAdom : IsDomain A := Function.Injective.isDomain (algebraMap A (Rh A)) algebraMap_Rh_injective

  haveI : IsPrincipalIdealRing (Rh A) := IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  have hprinc : (maximalIdeal A).IsPrincipal := by
    apply IsLocalRing.isPrincipal_of_isPrincipal_map_adicCompletion
    show (mh A).IsPrincipal
    exact IsPrincipalIdealRing.principal _

  have hnf : ¬ IsField A := by
    intro hF
    have h0 : maximalIdeal A = ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    have hmh : mh A = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [h0, Ideal.mem_bot] at ha
      rw [ha]; exact Ideal.zero_mem _
    have h1 : maximalIdeal (Rh A) = ⊥ := maximalIdeal_Rh.trans hmh

    have hX : ¬ IsUnit (e.symm PowerSeries.X) := fun h => by
      have := h.map e
      rw [RingEquiv.apply_symm_apply] at this
      have h2 := PowerSeries.isUnit_iff_constantCoeff.mp this
      rw [PowerSeries.constantCoeff_X] at h2
      exact not_isUnit_zero h2
    have hmem : e.symm PowerSeries.X ∈ maximalIdeal (Rh A) := (IsLocalRing.mem_maximalIdeal _).mpr hX
    rw [h1, Ideal.mem_bot, map_eq_zero_iff _ e.symm.injective] at hmem
    exact PowerSeries.X_ne_zero hmem
  exact ⟨hAdom, ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).mpr hprinc⟩

end
end S_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
end P2MW
export P2MW.S_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries (solution)
