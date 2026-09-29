-- Prove2me | solution 1 for KaehlerDifferential.exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e05658d8-9718-5c02-a378-ed75165b6ef0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct

namespace ConormalPresentation

open KaehlerDifferential

section Generic

variable (R : Type*) [CommRing R] (m : ℕ) (S : Type*) [CommRing S]
variable [Algebra R S] [Algebra (MvPolynomial (Fin m) R) S] [IsScalarTower R (MvPolynomial (Fin m) R) S]

local notation "P" => MvPolynomial (Fin m) R

noncomputable def bS : Module.Basis (Fin m) S (S ⊗[P] Ω[P⁄R]) := (mvPolynomialBasis R (Fin m)).baseChange S

noncomputable def coords : (Fin m → S) ≃ₗ[S] S ⊗[P] Ω[P⁄R] :=
  (Finsupp.linearEquivFunOnFinite S S (Fin m)).symm ≪≫ₗ (bS R m S).repr.symm

theorem coords_single (j : Fin m) : coords R m S (Pi.single j 1) = (1 : S) ⊗ₜ[P] D R P (MvPolynomial.X j) := by
  have h1 : (Finsupp.linearEquivFunOnFinite S S (Fin m)).symm (Pi.single j 1) = Finsupp.single j 1 := by
    ext i; simp [Finsupp.linearEquivFunOnFinite, Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [coords, LinearEquiv.trans_apply, h1, Module.Basis.repr_symm_single_one, bS, Module.Basis.baseChange_apply,
    mvPolynomialBasis_apply]

theorem coords_symm_tmul (w : Ω[P⁄R]) (j : Fin m) :
    (coords R m S).symm ((1 : S) ⊗ₜ[P] w) j = algebraMap P S ((mvPolynomialBasis R (Fin m)).repr w j) := by
  rw [coords, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.symm_symm,
    Finsupp.linearEquivFunOnFinite_apply, bS, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

theorem coords_symm_tmul_D (g : P) (j : Fin m) :
    (coords R m S).symm ((1 : S) ⊗ₜ[P] D R P g) j = algebraMap P S (MvPolynomial.pderiv j g) := by
  rw [coords_symm_tmul, mvPolynomialBasis_repr_apply]

noncomputable def Φ : (Fin m → S) →ₗ[S] Ω[S⁄R] := (mapBaseChange R P S) ∘ₗ (coords R m S).toLinearMap

theorem Φ_single (j : Fin m) : Φ R m S (Pi.single j 1) = D R S (algebraMap P S (MvPolynomial.X j)) := by
  rw [Φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, coords_single, mapBaseChange_tmul, one_smul, map_D]

theorem Φ_surjective (hφ : Function.Surjective (algebraMap P S)) : Function.Surjective (Φ R m S) :=
  (mapBaseChange_surjective R P S hφ).comp (coords R m S).surjective

theorem ker_mapBaseChange_eq {r : ℕ} (f : Fin r → P) (hφ : Function.Surjective (algebraMap P S))
    (hker : RingHom.ker (algebraMap P S) = Ideal.span (Set.range f)) :
    LinearMap.ker (mapBaseChange R P S) =
      Submodule.span S (Set.range fun i : Fin r => (1 : S) ⊗ₜ[P] D R P (f i)) := by
  classical
  have hex := exact_kerCotangentToTensor_mapBaseChange R P S hφ
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨c, hc⟩ := (hex w).mp hw
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [kerCotangentToTensor_toCotangent] at hc
    rw [← hc]
    have hx : (x : P) ∈ Ideal.span (Set.range f) := hker ▸ x.2
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
    rw [← ha, map_sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz, TensorProduct.tmul_add]
    have hfi : algebraMap P S (f i) = 0 := by
      have : f i ∈ RingHom.ker (algebraMap P S) := hker ▸ Ideal.subset_span (Set.mem_range_self i)
      exact this
    have h1 : (1 : S) ⊗ₜ[P] (f i • D R P (a i)) = 0 := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hfi, TensorProduct.zero_tmul]
    have h2 : (1 : S) ⊗ₜ[P] (a i • D R P (f i)) = algebraMap P S (a i) • ((1 : S) ⊗ₜ[P] D R P (f i)) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        smul_eq_mul, mul_one]
    rw [h2, h1, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply (hex _).mpr
    have hfi : f i ∈ RingHom.ker (algebraMap P S) := hker ▸ Ideal.subset_span (Set.mem_range_self i)
    exact ⟨(RingHom.ker (algebraMap P S)).toCotangent ⟨f i, hfi⟩, kerCotangentToTensor_toCotangent R P S _⟩

theorem ker_Φ {r : ℕ} (f : Fin r → P) (hφ : Function.Surjective (algebraMap P S))
    (hker : RingHom.ker (algebraMap P S) = Ideal.span (Set.range f)) :
    LinearMap.ker (Φ R m S) =
      Submodule.span S (Set.range fun i : Fin r => fun j : Fin m => algebraMap P S (MvPolynomial.pderiv j (f i))) := by
  rw [Φ, LinearMap.ker_comp, ker_mapBaseChange_eq R m S f hφ hker, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, funext fun j => (coords_symm_tmul_D R m S (f i) j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, funext fun j => coords_symm_tmul_D R m S (f i) j⟩

end Generic

end ConormalPresentation

theorem solution
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {m r : ℕ}
    (f : Fin r → MvPolynomial (Fin m) R) (φ : MvPolynomial (Fin m) R →ₐ[R] S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    ∃ Φ : (Fin m → S) →ₗ[S] Ω[S⁄R],
      Function.Surjective Φ ∧
      (∀ j : Fin m, Φ (Pi.single j 1) = KaehlerDifferential.D R S (φ (MvPolynomial.X j))) ∧
      LinearMap.ker Φ = Submodule.span S (Set.range fun i : Fin r => fun j : Fin m => φ (MvPolynomial.pderiv j (f i))) := by
  letI : Algebra (MvPolynomial (Fin m) R) S := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin m) R) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap R S x = φ (algebraMap R (MvPolynomial (Fin m) R) x)
      rw [AlgHom.commutes]
  have hmap : (algebraMap (MvPolynomial (Fin m) R) S : MvPolynomial (Fin m) R → S) = φ := rfl
  refine ⟨ConormalPresentation.Φ R m S, ConormalPresentation.Φ_surjective R m S (by rw [hmap]; exact hφ),
    fun j => ?_, ?_⟩
  · rw [ConormalPresentation.Φ_single]; rfl
  · rw [ConormalPresentation.ker_Φ R m S f (by rw [hmap]; exact hφ) (by ext x; exact Iff.of_eq (congrArg (x ∈ ·) hker))]
    rfl

end S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective
end P2MW
export P2MW.S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective (solution)
