-- Prove2me | solution 1 for NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7d698ce0-5f95-596c-af76-c50e108a3093

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_apply
import Theorems.Thm_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq
import Theorems.Thm_groupCohomology_pi_cocyclesMk_zsmul
import Theorems.Thm_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

set_option maxHeartbeats 12800000 in
theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (n : ℕ) (hn : Nat.card (K ≃ₐ[E] K) ∣ n)
    (f₁ : (Fin 3 → (K ≃ₐ[E] K)) → NumberField.SUnits.sUnitsRep E K S)
    (c : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SIdele.obj E K S)
    (hc : ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 2 3).hom c =
      fun g => (NumberField.SIdele.diag E K S).hom (f₁ g)) :
    ∃ (ω : (Fin 1 → (K ≃ₐ[E] K)) → NumberField.SIdele.obj E K S) (e : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SUnits.sUnitsRep E K S),
      (n : ℤ) • c = ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 1 2).hom ω + fun g => (NumberField.SIdele.diag E K S).hom (e g) := by
  classical

  have hx : ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.classObj E K S)).d 2 3).hom (fun g => (NumberField.SIdele.toClass E K S).hom (c g)) = 0 := by
    rw [groupCohomology.inhomogeneousCochains_d_comp_apply (NumberField.SIdele.toClass E K S) 2 c, hc]
    funext g
    exact (NumberField.SIdele.toClass_hom_apply_eq_zero_iff E K S _).2 ⟨_, rfl⟩

  have hG0 : (Nat.card (K ≃ₐ[E] K) : ℤ) • groupCohomology.π (NumberField.SIdele.classObj E K S) 2 (groupCohomology.cocyclesMk _ hx) = 0 := by
    obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup (K ≃ₐ[E] K)) (NumberField.SIdele.classObj E K S) 2
    have hres : (groupCohomology.map (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (𝟙 (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (NumberField.SIdele.classObj E K S))) 2).hom
        (groupCohomology.π (NumberField.SIdele.classObj E K S) 2 (groupCohomology.cocyclesMk _ hx)) = 0 :=
      (ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_succ_of_subsingleton (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (NumberField.SIdele.classObj E K S)) 1)).elim _ _
    have := hcor (groupCohomology.π (NumberField.SIdele.classObj E K S) 2 (groupCohomology.cocyclesMk _ hx))
    rw [hres, map_zero, Subgroup.index_bot] at this
    rw [natCast_zsmul]
    exact this.symm
  have hn0 : (n : ℤ) • groupCohomology.π (NumberField.SIdele.classObj E K S) 2 (groupCohomology.cocyclesMk _ hx) = 0 := by
    obtain ⟨m, rfl⟩ := hn
    rw [Nat.cast_mul, mul_comm, mul_smul, hG0]
    simp

  have hnx : ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.classObj E K S)).d 2 3).hom ((n : ℤ) • fun g => (NumberField.SIdele.toClass E K S).hom (c g)) = 0 := by
    rw [map_zsmul, hx]
    show (n : ℤ) • (0 : (groupCohomology.inhomogeneousCochains (NumberField.SIdele.classObj E K S)).X 3) = 0
    simp
  have h0 : ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.classObj E K S)).d 2 3).hom (0 : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SIdele.classObj E K S) = 0 := map_zero _
  have hcls : groupCohomology.π (NumberField.SIdele.classObj E K S) 2 (groupCohomology.cocyclesMk ((n : ℤ) • fun g => (NumberField.SIdele.toClass E K S).hom (c g)) hnx) =
      groupCohomology.π (NumberField.SIdele.classObj E K S) 2 (groupCohomology.cocyclesMk 0 h0) := by
    rw [groupCohomology.pi_cocyclesMk_zsmul _ 2 (n : ℤ) _ hx hnx, hn0,
      groupCohomology.pi_cocyclesMk_eq_zero_of_eq_zero _ 2 _ h0 rfl]
  obtain ⟨ωbar, hωbar⟩ := groupCohomology.exists_eq_add_d_of_pi_cocyclesMk_eq _ 1 _ _ hnx h0 hcls

  have hsurj : Function.Surjective (NumberField.SIdele.toClass E K S).hom :=
    GroupCohomology.RepCokernel.π_hom_surjective (NumberField.SIdele.diag E K S)
  choose ω hω using fun g : Fin 1 → (K ≃ₐ[E] K) => hsurj (ωbar g)
  have hωfun : (fun g => (NumberField.SIdele.toClass E K S).hom (ω g)) = ωbar := funext hω
  have hdiff : ∀ g : Fin 2 → (K ≃ₐ[E] K),
      ((n : ℤ) • c - ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 1 2).hom ω) g ∈
        Set.range (NumberField.SIdele.diag E K S).hom := fun g => by
    rw [← NumberField.SIdele.toClass_hom_apply_eq_zero_iff]
    have h2 : (NumberField.SIdele.toClass E K S).hom (((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 1 2).hom ω g) =
        (inhomogeneousCochains.d (NumberField.SIdele.classObj E K S) 1).hom ωbar g := by
      have := congrFun (groupCohomology.inhomogeneousCochains_d_comp_apply (NumberField.SIdele.toClass E K S) 1 ω) g
      rw [hωfun, groupCohomology.inhomogeneousCochains.d_def] at this
      exact this.symm
    have h1 : (n : ℤ) • (NumberField.SIdele.toClass E K S).hom (c g) =
        (inhomogeneousCochains.d (NumberField.SIdele.classObj E K S) 1).hom ωbar g := by
      have := congrFun hωbar g
      simp only [Pi.smul_apply, Pi.add_apply, Pi.zero_apply, zero_add] at this
      exact this
    rw [Pi.sub_apply, Pi.smul_apply, map_sub, map_zsmul, h1, h2, sub_self]
  choose e he using hdiff
  refine ⟨ω, e, ?_⟩
  funext g
  have := he g
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply] at this ⊢
  rw [this]
  abel

end S_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag
end P2MW
export P2MW.S_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag (solution)
