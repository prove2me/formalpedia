-- Prove2me | solution 1 for IsLocalRing.exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/23586302-2585-5562-b0db-08fab694ee73

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite

set_option autoImplicit false

open IsLocalRing

theorem solution
    {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S] (t : S)
    [Module.Finite A (S ⧸ Ideal.span ({t} : Set S))]
    (hinj : Function.Injective (algebraMap A (S ⧸ Ideal.span ({t} : Set S))))
    (hfib : ∀ s : S, ∃ a : A,
      s - algebraMap A S a ∈ Ideal.span ({t} : Set S) ⊔ (maximalIdeal A).map (algebraMap A S)) :
    ∃ χ : S →+* A, (∀ a : A, χ (algebraMap A S a) = a) ∧ RingHom.ker χ = Ideal.span ({t} : Set S) := by
  classical
  set I : Ideal S := Ideal.span ({t} : Set S) with hI
  set π : S →+* S ⧸ I := Ideal.Quotient.mk I with hπ
  have hφ : ∀ a : A, algebraMap A (S ⧸ I) a = π (algebraMap A S a) := fun a => rfl

  have hsurj : Function.Surjective (algebraMap A (S ⧸ I)) := by
    let N : Submodule A (S ⧸ I) := LinearMap.range (Algebra.linearMap A (S ⧸ I))
    have htop : (⊤ : Submodule A (S ⧸ I)) ≤ N ⊔ (maximalIdeal A) • (⊤ : Submodule A (S ⧸ I)) := by
      rintro m -
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨a, ha⟩ := hfib s
      have h1 : π (s - algebraMap A S a) ∈ (maximalIdeal A).map (algebraMap A (S ⧸ I)) := by
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ha
        rw [← huv, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hu, zero_add]
        have : (maximalIdeal A).map (algebraMap A (S ⧸ I)) = ((maximalIdeal A).map (algebraMap A S)).map π := by
          rw [Ideal.map_map]; rfl
        rw [this]
        exact Ideal.mem_map_of_mem _ hv
      rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at h1
      have h2 : π s = algebraMap A (S ⧸ I) a + π (s - algebraMap A S a) := by
        rw [hφ, ← map_add, add_sub_cancel]
      rw [h2]
      exact Submodule.add_mem_sup ⟨a, rfl⟩ h1
    have hN : (⊤ : Submodule A (S ⧸ I)) ≤ N :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) htop
    intro m
    obtain ⟨a, ha⟩ := hN (Submodule.mem_top : m ∈ ⊤)
    exact ⟨a, ha⟩
  let e : A ≃+* S ⧸ I := RingEquiv.ofBijective (algebraMap A (S ⧸ I)) ⟨hinj, hsurj⟩
  refine ⟨e.symm.toRingHom.comp π, fun a => ?_, ?_⟩
  · show e.symm (π (algebraMap A S a)) = a
    rw [← hφ]
    exact e.symm_apply_apply a
  · ext x
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.symm.injective]
    exact Ideal.Quotient.eq_zero_iff_mem

end S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite
end P2MW
export P2MW.S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite (solution)
