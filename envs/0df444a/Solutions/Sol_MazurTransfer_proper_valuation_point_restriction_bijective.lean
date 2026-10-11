-- Prove2me | solution 1 for MazurTransfer.proper_valuation_point_restriction_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T12:15:29.929993+00:00
-- url     : https://prove2.me/submissions/cfb01bf0-a309-4703-a57f-90fe3f05b51e

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. Design boundary: properness uniquely extends each fraction-field point over a valuation ring. Named downstream consumer: actual same-family rational Picard specialization maps. Reuses Mathlib valuative criterion and original FLT relative-point notation. -/
import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (B K : Type u) [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (t : Spec (.of B) ⟶ Spec (.of R)) :
    Function.Bijective (schemeHomOverComp (t := t) (f := f)
      (Spec.map (CommRingCat.ofHom (algebraMap B K))) rfl) := by
  let restrict : SchemeHomOver t f → SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap B K)) ≫ t) f :=
    schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap B K))) rfl
  have H : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  constructor
  · intro a b hab
    let S : ValuativeCommSq f :=
      { R := B, K := K, i₁ := (restrict a).val, i₂ := t,
        commSq := ⟨(restrict a).property⟩ }
    letI := (H S).some
    let la : S.commSq.LiftStruct := ⟨a.val,rfl,a.property⟩
    let lb : S.commSq.LiftStruct := ⟨b.val,(congrArg Subtype.val hab).symm,b.property⟩
    exact Subtype.ext (congrArg CommSq.LiftStruct.l (Subsingleton.elim la lb))
  · intro a
    let S : ValuativeCommSq f :=
      { R := B, K := K, i₁ := a.val, i₂ := t, commSq := ⟨a.property⟩ }
    let l := (H S).some.default
    exact ⟨⟨l.l,l.fac_right⟩,Subtype.ext l.fac_left⟩

#print axioms solution
