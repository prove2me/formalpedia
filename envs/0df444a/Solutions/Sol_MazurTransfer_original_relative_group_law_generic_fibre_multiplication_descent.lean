-- Prove2me | solution 1 for MazurTransfer.original_relative_group_law_generic_fibre_multiplication_descent
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T05:31:34.550342+00:00
-- url     : https://prove2.me/submissions/9e43c9ae-5398-4c36-a8a6-df3da28ddf28

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: multiplication preservation for the same two relative group laws descends from their generic fibres over the original domain when the original source is flat and target is separated.
Named downstream consumer: multiplication of the same selected integral order-thirteen norm maps and their kernel Hopf group laws.
-/
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
namespace MazurTransfer.OriginalRelativeGroupLawGenericFibreMultiplicationDescentBoundary20261020
end MazurTransfer.OriginalRelativeGroupLawGenericFibreMultiplicationDescentBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: multiplication preservation on the generic base-change
law descends to a flat source and separated target over a domain.
Named downstream consumer: the SAME selected integral order-13 norms.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
namespace MazurTransfer.OriginalRelativeGroupLawGenericFibreMultiplicationDescentProof20261020

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K]
  [Algebra R K] [IsFractionRing R K] {A B : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
  [Flat f] [IsSeparated g]
  (G : RelativeGroupLaw R f) (H : RelativeGroupLaw R g) (φ : SchemeHomOver f g)

theorem mul_of_genericFibre
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (RelativeGroupLaw.genericFibreStr K f)),
      NeronModelInfra.schemeHomOverComp ((G.genericFibre K).mul t x y)
        (genericFibreRestrict R K g f φ) =
      (H.genericFibre K).mul t
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K g f φ))
        (NeronModelInfra.schemeHomOverComp y (genericFibreRestrict R K g f φ)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.mul t x y) φ =
      H.mul t (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) := by
  apply Subtype.ext
  apply RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre R K H G φ
  intro S s a b
  let ι := specGenericFibreInclusion R K
  let a' : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f) :=
    RelativeGroupLaw.baseChangePointOfBase ι a
  let b' : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f) :=
    RelativeGroupLaw.baseChangePointOfBase ι b
  let φ' := genericFibreRestrict R K g f φ
  have h := hφ s a' b'
  have hh := congrArg (RelativeGroupLaw.baseChangePointToBase (f := g) ι) h
  have hG := RelativeGroupLaw.baseChangePointToBase_mul ι G s a' b'
  have hH := RelativeGroupLaw.baseChangePointToBase_mul ι H s
    (NeronModelInfra.schemeHomOverComp a' φ') (NeronModelInfra.schemeHomOverComp b' φ')
  have hleft := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K φ
    ((G.genericFibre K).mul s a' b')
  have ha := RelativeGroupLaw.baseChangePointToBase_ofBase ι a
  have hb := RelativeGroupLaw.baseChangePointToBase_ofBase ι b
  have hfa := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K φ a'
  have hfb := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K φ b'
  change RelativeGroupLaw.baseChangePointToBase ι a' = a at ha
  change RelativeGroupLaw.baseChangePointToBase ι b' = b at hb
  rw [ha, hb] at hG
  rw [ha] at hfa
  rw [hb] at hfb
  rw [hfa, hfb] at hH
  erw [hleft, hG, hH] at hh
  exact congrArg Subtype.val hh

end MazurTransfer.OriginalRelativeGroupLawGenericFibreMultiplicationDescentProof20261020

theorem solution : ∀ {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {A B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)} [Flat f] [IsSeparated g] (G : RelativeGroupLaw R f) (H : RelativeGroupLaw R g) (φ : SchemeHomOver f g), ∀ (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (RelativeGroupLaw.genericFibreStr K f)),
      NeronModelInfra.schemeHomOverComp ((G.genericFibre K).mul t x y)
        (genericFibreRestrict R K g f φ) =
      (H.genericFibre K).mul t
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K g f φ))
        (NeronModelInfra.schemeHomOverComp y (genericFibreRestrict R K g f φ)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f),
NeronModelInfra.schemeHomOverComp (G.mul t x y) φ =
      H.mul t (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) := by
  exact MazurTransfer.OriginalRelativeGroupLawGenericFibreMultiplicationDescentProof20261020.mul_of_genericFibre
#print axioms solution
