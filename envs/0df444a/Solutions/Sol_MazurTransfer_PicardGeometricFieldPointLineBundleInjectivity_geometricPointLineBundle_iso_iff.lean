-- Prove2me | solution 1 for MazurTransfer.PicardGeometricFieldPointLineBundleInjectivity.geometricPointLineBundle_iso_iff
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:01:45.501227+00:00
-- url     : https://prove2.me/submissions/b45255fe-5c0c-4dad-bb91-42485768e96f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: on an isomorphic model of the actual curve fibre, the
underlying line bundle detects equality of represented Picard field points.
Named downstream consumer: injectivity of the geometric arithmetic class
of the existing rational order-13 Picard scheme.
-/
import Definitions.Def_MazurTransfer_PicardCurvePullbackGeometricFieldLineBundleData


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer.PicardCurvePullbackGeometricFieldLineBundle
private def geometricIsoPullbackInvPullbackObj20261017 {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm

variable {R : Type u} [CommRing R] {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (j : X ⟶ pullback c t) [IsIso j]

theorem solution (a b : SchemeHomOver t D.toBase) :
    Nonempty (geometricPointLineBundle c ε D h t j a ≅
      geometricPointLineBundle c ε D h t j b) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    exact h.ext_of_iso t a b
      ⟨geometricIsoPullbackInvPullbackObj20261017 j (h.poincare.pullbackAlong a).L ≪≫
        (Scheme.Modules.pullback (inv j)).mapIso e ≪≫
        (geometricIsoPullbackInvPullbackObj20261017 j (h.poincare.pullbackAlong b).L).symm⟩
  · rintro rfl
    exact ⟨Iso.refl _⟩

#print axioms solution
