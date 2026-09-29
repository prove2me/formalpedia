-- Prove2me | solution 1 for KaehlerDifferential.exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b5f5fe6a-2a53-570f-b84d-3608e793b116

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S] [Module.Finite S Ω[S⁄R]]
    (π : S →ₐ[R] R) (t : S) (ht : π t = 0)
    (hcot : RingHom.ker π.toRingHom ≤ Ideal.span {t} ⊔ RingHom.ker π.toRingHom ^ 2)
    (ω : Ω[S⁄R]) :
    ∃ g : S, ω = g • KaehlerDifferential.D R S t := by
  classical
  set I : Ideal S := RingHom.ker π.toRingHom with hI
  have hmemI : ∀ x : S, x ∈ I ↔ π x = 0 := fun x => by rw [hI, RingHom.mem_ker]; rfl

  have hI_ne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : S) ∈ I := h ▸ Submodule.mem_top
    rw [hmemI, map_one] at h1

    have : (1 : S) = 0 := by
      have := congrArg (algebraMap R S) h1
      rwa [map_one, map_zero] at this
    exact one_ne_zero this
  have hI_jac : I ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hI_ne

  let N : Submodule S Ω[S⁄R] := Submodule.span S {KaehlerDifferential.D R S t}
  let E : Submodule S Ω[S⁄R] := N ⊔ I • ⊤

  have hD_sq : ∀ y ∈ I ^ 2, KaehlerDifferential.D R S y ∈ I • (⊤ : Submodule S Ω[S⁄R]) := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul ha Submodule.mem_top)
        (Submodule.smul_mem_smul hb Submodule.mem_top)
    · intro x y hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy

  have hD_mem : ∀ x : S, KaehlerDifferential.D R S x ∈ E := by
    intro x

    have hx1 : x - algebraMap R S (π x) ∈ I := by
      rw [hmemI, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hDx : KaehlerDifferential.D R S x = KaehlerDifferential.D R S (x - algebraMap R S (π x)) := by
      rw [map_sub, Derivation.map_algebraMap, sub_zero]
    rw [hDx]
    obtain ⟨st, hst, y, hy, hsum⟩ := Submodule.mem_sup.mp (hcot hx1)
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hst
    rw [← hsum, map_add, Derivation.leibniz]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    ·
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    ·
      refine Submodule.mem_sup_right (Submodule.smul_mem_smul ?_ Submodule.mem_top)
      rw [hmemI]; exact ht
    · exact Submodule.mem_sup_right (hD_sq y hy)

  have htop : (⊤ : Submodule S Ω[S⁄R]) ≤ E := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hD_mem x

  have hN : (⊤ : Submodule S Ω[S⁄R]) ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI_jac htop
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp (hN (Submodule.mem_top : ω ∈ ⊤))
  exact ⟨g, hg.symm⟩

end S_KaehlerDifferential_exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq
end P2MW
export P2MW.S_KaehlerDifferential_exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq (solution)
