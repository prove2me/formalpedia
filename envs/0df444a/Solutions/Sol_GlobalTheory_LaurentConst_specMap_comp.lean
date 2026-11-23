-- Prove2me | solution 1 for GlobalTheory.LaurentConst.specMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:45.642034+00:00
-- url     : https://prove2.me/submissions/0476ba45-db1f-4feb-a726-3a4ea22943cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (α : C →+* A)
    (β : D →+* C) {Y : Scheme.{0}} (f : Spec (.of D) ⟶ Y) :
    Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom β) ≫ f =
      Spec.map (CommRingCat.ofHom (α.comp β)) ≫ f := by
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
end GlobalTheory.LaurentConst
