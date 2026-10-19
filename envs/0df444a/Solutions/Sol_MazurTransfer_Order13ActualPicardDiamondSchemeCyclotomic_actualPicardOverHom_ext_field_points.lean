-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.actualPicardOverHom_ext_field_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:13:58.566924+00:00
-- url     : https://prove2.me/submissions/94e1481f-ced0-4c43-9f2e-548014794935

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: endomorphisms of the SAME actual rational Picard are
determined by every perfect characteristic-zero field point.
Named downstream consumer: genuine diamond cyclotomic and nineteen-norm
scheme identities. Original MazurTheorem field-point extensionality bridge.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardReducedProperGeometryData
import Theorems.Thm_MazurTransfer_RationalSchemeMorphismFieldPointExtensionality_hom_eq_of_field_points
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardReducedProperGeometry
local instance actualPicardFieldExtReduced20261017 : IsReduced actualPicard.P := actualPicard_reduced
local instance actualPicardFieldExtSeparated20261017 : IsSeparated actualPicard.toBase := actualPicard_separated
theorem solution
    (f g : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (H : ∀ (K : Type) [Field K] [CharZero K] [PerfectField K]
      (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase),
        a ≫ f = a ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply MazurTransfer.RationalSchemeMorphismFieldPointExtensionality.hom_eq_of_field_points
    actualPicard.toBase actualPicard.toBase f.left g.left (Over.w f) (Over.w g)
  intro K _ _ _ a ha
  exact congrArg (fun m => m.left) (H K (Over.homMk a ha))


#print axioms solution
