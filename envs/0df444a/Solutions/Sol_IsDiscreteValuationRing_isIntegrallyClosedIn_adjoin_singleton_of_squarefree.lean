-- Prove2me | solution 1 for IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3410221a-70dd-51b6-aec3-195e571cc9c0

import Mathlib
import Theorems.Thm_IsIntegrallyClosedIn_of_isReduced_quotient_span_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree

open Polynomial IsLocalRing

namespace DedekindCritField

theorem isReduced_quotient_span_singleton_of_squarefree {R : Type*} [CommRing R]
    [DecompositionMonoid R] {f : R} (hf : Squarefree f) : IsReduced (R ⧸ Ideal.span {f}) := by
  rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
  exact hf.isRadical

end DedekindCritField

open DedekindCritField in
theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    {α : F} (hα : IsIntegral O α)
    (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F ϖ ^ n * x ∈ Algebra.adjoin O {α}) :
    IsIntegrallyClosedIn (Algebra.adjoin O {α}) F := by
  set B : Subalgebra O F := Algebra.adjoin O {α} with hB
  have hinjOF : Function.Injective (algebraMap O F) := FaithfulSMul.algebraMap_injective O F
  have hϖF : algebraMap O F ϖ ≠ 0 := (map_ne_zero_iff _ hinjOF).mpr hϖ.ne_zero
  set ϖB : B := algebraMap O B ϖ with hϖB_def
  have hϖBval : (ϖB : F) = algebraMap O F ϖ := rfl
  have hϖB0 : ϖB ≠ 0 := fun h => hϖF (by rw [← hϖBval, h]; rfl)
  have hϖB : ϖB ∈ nonZeroDivisors B := mem_nonZeroDivisors_iff_ne_zero.mpr hϖB0

  haveI : IsReduced (B ⧸ Ideal.span {ϖB}) := by
    have hmax : (Ideal.span {ϖ}).IsMaximal := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]; infer_instance
    letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
    have e : AdjoinRoot (minpoly O α) ≃ₐ[O] B := minpoly.equivAdjoin hα
    have hJ : Ideal.span {ϖB} =
        Ideal.map (e : AdjoinRoot (minpoly O α) →+* B)
          (Ideal.map (AdjoinRoot.of (minpoly O α)) (Ideal.span {ϖ})) := by
      rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
      congr 2
      change algebraMap O B ϖ = e (algebraMap O (AdjoinRoot (minpoly O α)) ϖ)
      rw [AlgEquiv.commutes]
    let e1 := Ideal.quotientEquivAlg
      (Ideal.map (AdjoinRoot.of (minpoly O α)) (Ideal.span {ϖ})) (Ideal.span {ϖB}) e hJ
    let e2 := AdjoinRoot.quotEquivQuotMap (minpoly O α) (Ideal.span {ϖ})
    haveI : IsReduced ((O ⧸ Ideal.span {ϖ})[X] ⧸
        Ideal.span {(minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) :=
      isReduced_quotient_span_singleton_of_squarefree hsq
    exact isReduced_of_injective (e1.symm.trans e2).toRingEquiv (e1.symm.trans e2).toRingEquiv.injective

  haveI : IsLocalization.Away ϖB F := by
    refine IsLocalization.Away.mk ϖB ?_ ?_ ?_
    · exact isUnit_iff_ne_zero.mpr (by rw [show algebraMap B F ϖB = algebraMap O F ϖ from rfl]; exact hϖF)
    · intro s
      obtain ⟨n, hn⟩ := hgen s
      refine ⟨n, ⟨_, hn⟩, ?_⟩
      change s * (algebraMap O F ϖ) ^ n = algebraMap O F ϖ ^ n * s
      ring
    · intro a b h
      exact ⟨0, by simpa using Subtype.val_injective h⟩
  exact IsIntegrallyClosedIn.of_isReduced_quotient_span_singleton ϖB hϖB F

end S_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree
end P2MW
export P2MW.S_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree (solution)
