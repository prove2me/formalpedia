-- Prove2me | solution 1 for GlobalTheory.finite_group_invariants_and_norms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:10.238582+00:00
-- url     : https://prove2.me/submissions/a1bcdcfe-3fd4-4da6-8fc2-be0eda822aae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isIntegral_fixedSubring
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_of_isInvariant
import Theorems.Thm_GlobalTheory_finite_fixedSubalgebra
import Theorems.Thm_GlobalTheory_finiteType_fixedSubalgebra
import Theorems.Thm_GlobalTheory_exists_orbit_eq_primesOver
import Theorems.Thm_GlobalTheory_mem_baseChange_invariants_iff
import Theorems.Thm_GlobalTheory_injective_baseChange_invariants_subtype
import Theorems.Thm_GlobalTheory_isBaseChange_fixedSubalgebra_tensor
import Theorems.Thm_GlobalTheory_localizationMulSemiringAction_smulDistribClass
import Theorems.Thm_GlobalTheory_isInvariant_of_isLocalization
import Theorems.Thm_GlobalTheory_invertible_of_bijective_toSpanSingleton
import Theorems.Thm_GlobalTheory_free_of_invertible_of_finite_maximalSpectrum
import Theorems.Thm_GlobalTheory_exists_bijective_toSpanSingleton_of_finite_maximalSpectrum
import Theorems.Thm_GlobalTheory_smul_tensorNorm
import Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_tensorNorm
import Theorems.Thm_GlobalTheory_exists_unit_tensorNorm_eq
import Theorems.Thm_GlobalTheory_forall_smul_eq_iff_tensorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
universe u v
namespace GlobalTheory
theorem _root_.solution (G : Type v) [Group G] [Finite G]
    (A : Type u) [CommRing A] [MulSemiringAction G A] :
    Algebra.IsIntegral (FixedPoints.subring A G) A ∧
    (IsDomain A → IsIntegrallyClosed A →
      IsDomain (FixedPoints.subring A G) ∧ IsIntegrallyClosed (FixedPoints.subring A G)) ∧
    (∀ (R : Type u) [CommRing R] [Algebra R A] [SMulCommClass G R A] [IsNoetherianRing R]
      [Algebra.FiniteType R A],
      Algebra.FiniteType R (FixedPoints.subalgebra R A G) ∧
        Module.Finite (FixedPoints.subalgebra R A G) A) ∧
    (∀ (P : Ideal (FixedPoints.subring A G)) [P.IsPrime],
      ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A) ∧
    (∀ (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
      [AddCommGroup M] [Module R M] (ρ : Representation R G M),
      Function.Injective (ρ.invariants.subtype.baseChange S) ∧
        ∀ x : S ⊗[R] M, x ∈ ρ.invariants.baseChange S ↔ ∀ g, (ρ g).baseChange S x = x) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra R A]
      [SMulCommClass G R A],
      letI := tensorMulSemiringAction G R S A
      haveI := tensorMulSemiringAction_smulCommClass G R S A
      IsBaseChange S (fixedSubalgebraMap G S
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
        (tensorMulSemiringAction_includeRight G R S A)).toLinearMap) ∧
    (∀ T : Submonoid (FixedPoints.subring A G),
      letI := localizationMulSemiringAction G (Algebra.algebraMapSubmonoid A T)
        (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
      Function.Injective
        (algebraMap (Localization T) (Localization (Algebra.algebraMapSubmonoid A T))) ∧
      ∀ x : Localization (Algebra.algebraMapSubmonoid A T),
        (∀ g : G, g • x = x) ↔ ∃ y : Localization T, algebraMap _ _ y = x) ∧
    (∀ (M : Type u) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
      (κ : Fin (Nat.card G) ≃ G) (e : M),
      Function.Bijective (LinearMap.toSpanSingleton A M e) →
      letI := piTensorDistribMulAction G A (fun _ : Fin (Nat.card G) ↦ M)
      Function.Bijective
        (LinearMap.toSpanSingleton A (⨂[A]^(Nat.card G) M) (tensorNorm A κ e)) ∧
      (∀ g : G, g • tensorNorm A κ e = tensorNorm A κ e) ∧
      (∀ e' : M, Function.Bijective (LinearMap.toSpanSingleton A M e') →
        ∃ u : (FixedPoints.subring A G)ˣ,
          tensorNorm A κ e' = ((u : FixedPoints.subring A G) : A) • tensorNorm A κ e) ∧
      ∀ y : ⨂[A]^(Nat.card G) M,
        (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • tensorNorm A κ e) ∧
    (∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Invertible A M],
      Finite (MaximalSpectrum A) →
        Module.Free A M ∧ ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e)) := by
  refine ⟨isIntegral_fixedSubring A G, fun _ _ ↦ isIntegrallyClosed_of_isInvariant A G _,
    fun R _ _ _ _ _ ↦ ⟨finiteType_fixedSubalgebra A G R, finite_fixedSubalgebra A G R⟩,
    fun P _ ↦ exists_orbit_eq_primesOver A G P,
    fun R S M _ _ _ _ _ _ ρ ↦
      ⟨injective_baseChange_invariants_subtype S ρ, mem_baseChange_invariants_iff S ρ⟩,
    fun R S _ _ _ _ _ _ ↦ isBaseChange_fixedSubalgebra_tensor G R S A, fun T ↦ ?_,
    fun M _ _ _ _ κ e he ↦ ⟨bijective_toSpanSingleton_tensorNorm κ he, ?_,
      fun e' he' ↦ exists_unit_tensorNorm_eq κ he he', forall_smul_eq_iff_tensorNorm κ he⟩,
    fun M _ _ _ _ ↦ ⟨free_of_invertible_of_finite_maximalSpectrum A M,
      exists_bijective_toSpanSingleton_of_finite_maximalSpectrum A M⟩⟩
  · letI := localizationMulSemiringAction G (Algebra.algebraMapSubmonoid A T)
      (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
    haveI := localizationMulSemiringAction_smulDistribClass G (Algebra.algebraMapSubmonoid A T)
      (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
    obtain ⟨h1, h2, h3⟩ := isInvariant_of_isLocalization G (A := A) T (Localization T)
      (Localization (Algebra.algebraMapSubmonoid A T))
    haveI := h3 inferInstance
    refine ⟨FaithfulSMul.algebraMap_injective _ _, fun x ↦ ⟨h2.isInvariant x, ?_⟩⟩
    rintro ⟨y, rfl⟩ g
    exact smul_algebraMap g y
  · haveI := invertible_of_bijective_toSpanSingleton he
    exact smul_tensorNorm A κ e
end GlobalTheory
