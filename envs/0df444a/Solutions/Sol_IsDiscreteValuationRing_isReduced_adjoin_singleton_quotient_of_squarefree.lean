-- Prove2me | solution 1 for IsDiscreteValuationRing.isReduced_adjoin_singleton_quotient_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b5e877ad-d3b9-5e4b-92ec-62a5411d9703

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_isReduced_adjoin_singleton_quotient_of_squarefree

open Polynomial IsLocalRing

theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    {α : F} (hα : IsIntegral O α)
    (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ})))) :
    IsReduced (Algebra.adjoin O {α} ⧸
      Ideal.span {algebraMap O (Algebra.adjoin O {α}) ϖ}) := by
  set B : Subalgebra O F := Algebra.adjoin O {α}
  set ϖB : B := algebraMap O B ϖ
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
      Ideal.span {(minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    exact hsq.isRadical
  exact isReduced_of_injective (e1.symm.trans e2).toRingEquiv (e1.symm.trans e2).toRingEquiv.injective

end S_IsDiscreteValuationRing_isReduced_adjoin_singleton_quotient_of_squarefree
end P2MW
export P2MW.S_IsDiscreteValuationRing_isReduced_adjoin_singleton_quotient_of_squarefree (solution)
