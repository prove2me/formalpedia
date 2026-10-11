-- Prove2me | solution 1 for MazurTransfer.picard_curve_fibre_line_bundle_detects_field_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T17:45:48.402773+00:00
-- url     : https://prove2.me/submissions/3ec8801b-afbb-4c89-90bc-2bf5d96a6d0c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an isomorphic actual curve fibre model detects equality of
represented Picard field points by its pulled-back Poincare line bundles.
Named downstream consumer: injectivity of the geometric arithmetic class of
the existing rational order-13 Picard, then geometric scheme identities.
-/
noncomputable section
namespace PicardGeometricLineBundleInjectivityPublicProof
private def recover {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIso j] (M : Y.Modules) :
    M ≅ (Scheme.Modules.pullback (inv j)).obj ((Scheme.Modules.pullback j).obj M) :=
  ((Scheme.Modules.pullbackComp (inv j) j).app M ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id j)).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M).symm
end PicardGeometricLineBundleInjectivityPublicProof

theorem solution
    {R : Type u} [CommRing R] {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε P D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (j : X ⟶ pullback c t) [IsIso j]
    (a b : SchemeHomOver t D.toBase) :
    Nonempty ((Scheme.Modules.pullback j).obj (h.poincare.pullbackAlong a).L ≅
      (Scheme.Modules.pullback j).obj (h.poincare.pullbackAlong b).L) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    exact h.ext_of_iso t a b
      ⟨PicardGeometricLineBundleInjectivityPublicProof.recover j (h.poincare.pullbackAlong a).L ≪≫
        (Scheme.Modules.pullback (inv j)).mapIso e ≪≫
        (PicardGeometricLineBundleInjectivityPublicProof.recover j (h.poincare.pullbackAlong b).L).symm⟩
  · rintro rfl
    exact ⟨Iso.refl _⟩

#print axioms solution
