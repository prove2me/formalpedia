-- Prove2me | solution 1 for Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/057e6ccb-79fa-5ff3-b6ac-92665e5fc3b3

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
import Theorems.Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range

set_option autoImplicit false

universe u

open TensorProduct

namespace P2mB1

theorem ker_le_range_of_conj {A : Type*} [Semiring A]
    {X Y Z X' Y' Z' : Type*} [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [Module A X] [Module A Y] [Module A Z] [Module A X'] [Module A Y'] [Module A Z']
    (eX : X' ≃ₗ[A] X) (eY : Y' ≃ₗ[A] Y) (eZ : Z' ≃ₗ[A] Z)
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (f' : X' →ₗ[A] Y') (g' : Y' →ₗ[A] Z')
    (hf : f' = (eY.symm : Y →ₗ[A] Y') ∘ₗ f ∘ₗ (eX : X' →ₗ[A] X))
    (hg : g' = (eZ.symm : Z →ₗ[A] Z') ∘ₗ g ∘ₗ (eY : Y' →ₗ[A] Y))
    (h : LinearMap.ker g ≤ LinearMap.range f) :
    LinearMap.ker g' ≤ LinearMap.range f' := by
  intro y hy
  rw [LinearMap.mem_ker, hg, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff] at hy
  obtain ⟨x, hx⟩ := h hy
  refine ⟨eX.symm x, ?_⟩
  rw [hf, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, hx, LinearEquiv.symm_apply_apply]

theorem subsingleton_tensor {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Subsingleton M] : Subsingleton (S ⊗[R] M) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : S ⊗[R] M, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h x, h y]

end P2mB1

open P2mB1 in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S],
        ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S) := by
  classical

  let S₀ : Type u := Localization.AtPrime 𝔭.asIdeal
  have hex₀ : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S₀) ≤ LinearMap.range ((d i).baseChange S₀) := by
    have key := Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
      (R := S₀) (fun i => S₀ ⊗[R] C i) (fun i => (d i).baseChange S₀) ?_ n ?_ ?_ ?_
    · exact key.1
    · intro i
      show (d (i + 1)).baseChange S₀ ∘ₗ (d i).baseChange S₀ = 0
      rw [← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero]
    · intro i hi
      haveI := hbd i hi
      exact subsingleton_tensor S₀ (C i)
    · intro i
      exact (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv S₀ (d i)
        (d (i + 1)) (hdd i)).2.2.2 (hfin i)
    · intro i
      exact ker_le_range_of_conj
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S₀ _ _ (C i))
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S₀ _ _ (C (i + 1)))
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S₀ _ _ (C (i + 1 + 1)))
        _ _ _ _ (LinearMap.baseChange_baseChange (d i)) (LinearMap.baseChange_baseChange (d (i + 1))) (hfib i)

  have hsub₀ : ∀ i : ℕ, Subsingleton (S₀ ⊗[R]
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :=
    fun i => (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv S₀ (d i)
        (d (i + 1)) (hdd i)).2.2.1.mp (hex₀ i)
  have ha : ∀ i : ℕ, ∃ a : R, a ∉ 𝔭.asIdeal ∧ Subsingleton (LocalizedModule.Away a
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) := by
    intro i
    haveI := hfin i
    haveI := hsub₀ i
    obtain ⟨a, ha, hs⟩ := IsLocalizedModule.exists_subsingleton_away
      (TensorProduct.mk R S₀ (LinearMap.ker (d (i + 1)) ⧸
        (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) 1) 𝔭.asIdeal
    exact ⟨a, ha, hs⟩
  choose a ha hsa using ha
  refine ⟨∏ i ∈ Finset.range n, a i, ?_, ?_⟩
  · exact fun hmem => by
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact ha i hi
  · intro S _ _ _ i
    haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers (∏ i ∈ Finset.range n, a i))
    refine (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv S (d i)
        (d (i + 1)) (hdd i)).2.2.1.mpr ?_
    rw [IsLocalizedModule.subsingleton_iff (Submonoid.powers (∏ i ∈ Finset.range n, a i))
      (TensorProduct.mk R S (LinearMap.ker (d (i + 1)) ⧸
        (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) 1)]
    intro m
    by_cases hi : i < n
    · obtain ⟨r, ⟨k, rfl⟩, hr⟩ := (LocalizedModule.subsingleton_iff.mp (hsa i)) m
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_range.mpr hi)
      refine ⟨(∏ i ∈ Finset.range n, a i) ^ k, ⟨k, rfl⟩, ?_⟩
      rw [hc, mul_pow, mul_comm, mul_smul, hr, smul_zero]
    · refine ⟨1, Submonoid.one_mem _, ?_⟩
      haveI : Subsingleton (C (i + 1)) := hbd (i + 1) (by omega)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [one_smul, show x = 0 from Subtype.ext (Subsingleton.elim _ _), Submodule.Quotient.mk_zero]

end S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
end P2MW
export P2MW.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range (solution)
