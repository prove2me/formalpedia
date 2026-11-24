-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.flat_splitTorusAff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:19.765881+00:00
-- url     : https://prove2.me/submissions/69cb8033-3623-4d5f-b502-0c57443c5b71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
open ReciprocityTheory.ChartRestriction.G.Semi
variable (X : Type u) [AddCommGroup X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
theorem _root_.solution : Flat (splitTorusAff ZU X).hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap ZU (torusRing ZU X))))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)).Flat
  rw [RingHom.flat_algebraMap_iff]
  have : Module.Free (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X) := inferInstance
  infer_instance
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
