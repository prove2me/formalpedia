-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f6043718-2a08-5388-8651-afabf0e112b0

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {M : Type*} [CommGroup M] (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ (D.unitsAct σ z) = ξ z)
    (n : (AdeleRing (𝓞 L) L)ˣ) (hn : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm n = 1) :
    ξ n = 1 := by
  classical
  obtain ⟨-, -, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D

  have h1 : ∏ τ : L ≃ₐ[K] L, D.unitsAct τ n = 1 := by
    rw [hprod n, hn, map_one]

  have hcard : orderOf σ = Fintype.card (L ≃ₐ[K] L) := by
    rw [← Nat.card_eq_fintype_card]; exact orderOf_eq_card_of_forall_mem_zpowers hgen
  have hinj : Set.InjOn (fun k : ℕ => σ ^ k) (Finset.range (orderOf σ) : Set ℕ) := by
    intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
  have himage : (Finset.range (orderOf σ)).image (fun k : ℕ => σ ^ k) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, hcard]
  have h2 : ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) n = 1 := by
    have := Finset.prod_image (f := fun τ : L ≃ₐ[K] L => D.unitsAct τ n) hinj
    rw [himage] at this
    rw [← this, h1]
  obtain ⟨w, hw⟩ :=
    M4aHerbrand.IdeleGaloisDescent.exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one K L σ D n h2
  rw [hw, map_mul, map_inv, hξ, inv_mul_cancel]

end S_M4aHerbrand_IdeleGaloisDescent_apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_apply_eq_one_of_idelicNorm_eq_one_of_forall_apply_unitsAct_eq (solution)
