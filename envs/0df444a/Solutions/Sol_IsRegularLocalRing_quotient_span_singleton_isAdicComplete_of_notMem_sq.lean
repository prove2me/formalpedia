-- Prove2me | solution 1 for IsRegularLocalRing.quotient_span_singleton_isAdicComplete_of_notMem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e081afcc-a111-5270-bb30-db47ca41a1a7

import Mathlib
import Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
import Theorems.Thm_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_quotient_span_singleton_isAdicComplete_of_notMem_sq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R] [IsAdicComplete (maximalIdeal R) R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) (hx0 : x ≠ 0)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧ IsDomain (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R ∧
      IsAdicComplete (maximalIdeal (R ⧸ Ideal.span {x})) (R ⧸ Ideal.span {x}) ∧
      maximalIdeal (R ⧸ Ideal.span {x}) = (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) := by
  obtain ⟨hreg, hdim⟩ :=
    RegularQuotientEngine.isRegularLocalRing_quotient_and_ringKrullDim_succ_eq R hx hx2
  obtain ⟨hP, -, -⟩ :=
    IsRegularLocalRing.isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
      R x hx hx2 hx0
  have hdom : IsDomain (R ⧸ Ideal.span {x}) := (Ideal.Quotient.isDomain_iff_prime _).mpr hP
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {x})) := Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal (R ⧸ Ideal.span {x}) =
      (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) := by
    have hcomap : (maximalIdeal (R ⧸ Ideal.span {x})).comap (Ideal.Quotient.mk (Ideal.span {x})) =
        maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hsurj)
    rw [← hcomap, Ideal.map_comap_of_surjective _ hsurj]
  have h1 : IsAdicComplete (maximalIdeal R) (R ⧸ Ideal.span {x}) := by
    have hH : IsHausdorff (maximalIdeal R) (R ⧸ Ideal.span {x}) := inferInstance
    have hPc : IsPrecomplete (maximalIdeal R) (R ⧸ Ideal.span {x}) := by
      rw [← AdicCompletion.of_surjective_iff]
      intro c
      obtain ⟨c', rfl⟩ := AdicCompletion.map_surjective (maximalIdeal R)
        (f := Submodule.mkQ (Ideal.span {x})) (Submodule.mkQ_surjective _) c
      obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective (maximalIdeal R) R c'
      exact ⟨Submodule.mkQ _ r, (AdicCompletion.map_of _ _ _).symm⟩
    exact (isAdicComplete_iff _ _).mpr ⟨hH, hPc⟩
  have h2 : IsAdicComplete ((maximalIdeal R).map (algebraMap R (R ⧸ Ideal.span {x})))
      (R ⧸ Ideal.span {x}) :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) (R ⧸ Ideal.span {x})).mpr h1
  have hcomplete : IsAdicComplete (maximalIdeal (R ⧸ Ideal.span {x})) (R ⧸ Ideal.span {x}) := by
    rw [hmax, ← Ideal.Quotient.algebraMap_eq]
    exact h2
  exact ⟨hreg, hdom, hdim, hcomplete, hmax⟩

end S_IsRegularLocalRing_quotient_span_singleton_isAdicComplete_of_notMem_sq
end P2MW
export P2MW.S_IsRegularLocalRing_quotient_span_singleton_isAdicComplete_of_notMem_sq (solution)
