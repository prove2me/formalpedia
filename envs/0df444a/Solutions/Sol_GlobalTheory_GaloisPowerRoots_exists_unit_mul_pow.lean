-- Prove2me | solution 1 for GlobalTheory.GaloisPowerRoots.exists_unit_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:48.344195+00:00
-- url     : https://prove2.me/submissions/2fbf64ab-3fae-4582-acfe-1ec4fc4bc074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_sub_mem_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots
namespace GlobalTheory.GaloisPowerRoots
theorem _root_.solution {R : Type*} (K L : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosure R L)] :
    ∃ (u : (integralClosure R L)ˣ) (ϖ : integralClosure R L),
      algebraMap R _ π = u * ϖ ^ Module.finrank K L := by
  set S := integralClosure R L
  haveI : FaithfulSMul R L := FaithfulSMul.trans R K L
  haveI : FaithfulSMul R S := FaithfulSMul.tower_bot R S L
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain R K L
  haveI : Module.Finite R S := IsIntegralClosure.finite R K L S
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  have hp0 : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hnf : ¬ IsField S := fun h => IsDiscreteValuationRing.not_isField R
    ((Algebra.IsIntegral.isField_iff_isField (FaithfulSMul.algebraMap_injective R S)).mpr h)
  haveI : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 0 2).mpr (inferInstance : IsDedekindDomain S)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hπ0 : algebraMap R S π ≠ 0 := by simpa using hπ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hϖ
  refine ⟨u, ϖ, ?_⟩
  have h1 := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0
  have h2 : (maximalIdeal R).inertiaDeg' (maximalIdeal S) = 1 := by
    rw [Ideal.inertiaDeg'_algebraMap]
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    letI : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
    refine Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨RingHom.injective _, fun x => ?_⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := exists_sub_mem_maximalIdeal (A := R) t
    exact ⟨Ideal.Quotient.mk _ a, (Ideal.Quotient.eq.mpr ha).symm⟩
  have hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S ^ e := by
    rw [hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu,
      Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  have h3 : Ideal.ramificationIdx' (maximalIdeal R) (maximalIdeal S) = e := by
    refine Ideal.ramificationIdx'_spec hmap.le ?_
    rw [hmap]
    exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) e).not_ge
  rw [h2, h3, mul_one] at h1
  rw [← h1, hu]
end GlobalTheory.GaloisPowerRoots
