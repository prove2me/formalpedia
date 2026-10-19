-- Prove2me | solution 1 for MazurTransfer.Order13EveryRepresentedIntegralPicardGeometry.every_represented_integral_picard_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T03:39:07.00646+00:00
-- url     : https://prove2.me/submissions/c1e5feef-d633-45ae-a053-15bcf61c7e3a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every genuine representation of the actual integral
order-13 Picard functor inherits smooth, proper and geometrically
connected geometry through its canonical representing isomorphism.
Named downstream consumer: local abelian models of the SAME selected
integral Picard family used for rational norm extension.
-/
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_PicardCanonicalRepresentationGroupIsomorphism
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardRepresentation_actual_integral_picard_representation

noncomputable section
universe u
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open PicardCanonicalRepresentationGroupIsomorphism

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) (D : RelativePic0Designation R (curveToBase R))
    (hD : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  obtain ⟨E, ⟨hE⟩, hs, hp, hg⟩ :=
    Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation R h104
  letI := hs
  letI := hp
  letI := hg
  let e := canonicalSchemeIso (P := algEquivZeroGroupCut (curveToBase R)
    (positiveInfinitySection R)) hD hE
  have he : e.hom ≫ E.toBase = D.toBase := canonicalSchemeIso_over _ _
  rw [← he]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [GeometricallyConnected.eq_geometrically] at hg ⊢
  exact (MorphismProperty.cancel_left_of_respectsIso (P := geometrically (ConnectedSpace ·))
    e.hom E.toBase).2 hg

#print axioms solution
