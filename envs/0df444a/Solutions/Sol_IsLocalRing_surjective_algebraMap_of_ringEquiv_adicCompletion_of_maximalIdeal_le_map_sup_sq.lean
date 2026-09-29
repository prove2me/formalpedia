-- Prove2me | solution 1 for IsLocalRing.surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/48bc33fa-6434-588d-8541-1ef9e4425f03

import Mathlib
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq

set_option autoImplicit false

theorem solution
    {R S M : Type*} [CommRing R] [CommRing S] [CommRing M]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S] [IsNoetherianRing S] [IsLocalRing M] [IsNoetherianRing M]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    (hres : ∀ s : S, ∃ r : R, s - algebraMap R S r ∈ IsLocalRing.maximalIdeal S)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* M)
    (hcot : IsLocalRing.maximalIdeal M ≤
      (IsLocalRing.maximalIdeal R).map (ι.toRingHom.comp ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp
        (algebraMap R S))) ⊔ IsLocalRing.maximalIdeal M ^ 2) :
    Function.Surjective (algebraMap R S) := by
  classical

  have hfgM : (IsLocalRing.maximalIdeal M : Submodule M M).FG := (isNoetherian_def.mp inferInstance) _
  have hA : IsLocalRing.maximalIdeal M ≤
      (IsLocalRing.maximalIdeal R).map (ι.toRingHom.comp ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp (algebraMap R S))) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfgM (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    rw [smul_eq_mul, ← pow_two]
    exact hcot

  have hB : (IsLocalRing.maximalIdeal M).comap ι.toRingHom
      ≤ ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := by
    have h1 := Ideal.comap_mono (f := ι.toRingHom) hA
    have h2 : ((IsLocalRing.maximalIdeal R).map (ι.toRingHom.comp ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp (algebraMap R S)))).comap ι.toRingHom
        = (IsLocalRing.maximalIdeal R).map ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp (algebraMap R S)) := by
      rw [← Ideal.map_map ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp (algebraMap R S)) ι.toRingHom]
      exact Ideal.comap_map_of_bijective _ ι.bijective
    rw [h2, ← Ideal.map_map (algebraMap R S) (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))] at h1
    exact h1

  have hC : IsLocalRing.maximalIdeal S ≤ ((IsLocalRing.maximalIdeal M).comap ι.toRingHom).comap (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := by
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hunit' : IsUnit ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) s) := by
      have h1 : IsUnit (ι.symm.toRingHom (ι.toRingHom ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) s))) := hunit.map ι.symm.toRingHom
      have e : ι.symm.toRingHom (ι.toRingHom ((algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) s)) = (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) s := ι.symm_apply_apply _
      rw [e] at h1
      exact h1
    rw [AdicCompletion.algebraMap_apply] at hunit'
    have hlev := hunit'.map (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1)
    rw [AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply] at hlev
    have hzero : Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ 1) s = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact hs
    rw [hzero, isUnit_zero_iff] at hlev
    have hne : (IsLocalRing.maximalIdeal S ^ 1) ≠ ⊤ := by
      rw [pow_one]
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    exact hne (Ideal.Quotient.zero_eq_one_iff.mp hlev)

  have hD : IsLocalRing.maximalIdeal S ≤ (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
    have := le_trans hC (Ideal.comap_mono (f := (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))) hB)
    rwa [IsLocalRing.comap_map_adicCompletion_eq] at this

  have key : (⊤ : Submodule R S) ≤ LinearMap.range (Algebra.linearMap R S) ⊔ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S) := by
    intro s _
    obtain ⟨r, hr⟩ := hres s
    have hmem : s - algebraMap R S r ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S) := by
      rw [Ideal.smul_top_eq_map]
      exact hD hr
    have : s = algebraMap R S r + (s - algebraMap R S r) := by ring
    rw [this]
    exact Submodule.add_mem_sup ⟨r, rfl⟩ hmem
  have htop : (⊤ : Submodule R S) ≤ LinearMap.range (Algebra.linearMap R S) :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) key
  intro s
  obtain ⟨r, hr⟩ := htop (Submodule.mem_top : s ∈ (⊤ : Submodule R S))
  exact ⟨r, hr⟩

end S_IsLocalRing_surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq
end P2MW
export P2MW.S_IsLocalRing_surjective_algebraMap_of_ringEquiv_adicCompletion_of_maximalIdeal_le_map_sup_sq (solution)
