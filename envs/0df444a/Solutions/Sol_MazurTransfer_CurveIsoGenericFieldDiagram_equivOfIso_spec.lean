-- Prove2me | solution 1 for MazurTransfer.CurveIsoGenericFieldDiagram.equivOfIso_spec
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:04:01.989164+00:00
-- url     : https://prove2.me/submissions/5c4f12d6-7a37-4eeb-bc34-27299b0618e7

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complete checked FLT function-field pullback associated
to a curve isomorphism commutes with its actual generic-stalk embedding.
Named downstream consumer: Order13ActualGeometricGaloisSemilinearAutomorphism.
-/
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018

noncomputable section
universe u
open MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull
open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem solution (e : X ≅ Y) :
    Spec.map (CommRingCat.ofHom (equivOfIso e).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ e.hom := by
  change Spec.map (pull e.hom (specializes_of_iso e)) ≫ _ = _
  simp only [pull, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]


#print axioms solution
