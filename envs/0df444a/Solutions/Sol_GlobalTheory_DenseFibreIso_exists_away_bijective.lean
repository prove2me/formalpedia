-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.exists_away_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:55.637154+00:00
-- url     : https://prove2.me/submissions/0645da1e-96a4-4116-9db7-85fc5f8675f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_smul_eq_zero
import Theorems.Thm_GlobalTheory_DenseFibreIso_subsingleton_of_isUnit
import Theorems.Thm_GlobalTheory_DenseFibreIso_includeLeft_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {A : Type} [CommRing A]
variable {B : Type} [CommRing B] [Algebra A B]
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution [IsNoetherianRing A] (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  let I : Submodule A A := LinearMap.ker (Algebra.linearMap A B)
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := LinearMap.exact_subtype_ker_map _
  have hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj K _).1
      (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs
        (I.subtype.restrictScalars R) Subtype.val_injective hex K)
  have h1 : Subsingleton (I ⊗[R] K) := by
    refine subsingleton_of_forall_eq 0 fun z => hinj (h ?_)
    rw [map_zero, map_zero]
    induction z with
    | zero => rw [map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
    | tmul x c =>
      have e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have hx : (x : A) • (1 : B) = 0 := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact x.2
      change ((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0
      rw [e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]
  have h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I) :=
    ((TensorProduct.comm A _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton
  obtain ⟨a, ha, ha'⟩ := exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m
  refine ⟨a, ha, ?_⟩
  have h3 := subsingleton_of_isUnit ha' (Localization.Away a)
    (IsLocalization.Away.algebraMap_isUnit a)
  rw [includeLeft_eq, EquivLike.bijective_comp]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩
  obtain ⟨y, rfl⟩ := (lTensor_exact (Localization.Away a) hex hs z).1 hz
  rw [Subsingleton.elim y 0, map_zero]
end GlobalTheory.DenseFibreIso
