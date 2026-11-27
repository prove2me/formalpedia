-- Prove2me | solution 1 for GlobalTheory.unitOf_bijective_mul_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:24.380988+00:00
-- url     : https://prove2.me/submissions/1d5832b2-f4c8-48aa-ae15-26c1e6d2c71f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_bijective
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_mul
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_ptMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O], (∀ (R : Type) [CommRing R] [Algebra O R], Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) ∧ ∀ w w' : specO O R ⟶ Gm (Spec (CommRingCat.of O)), unitOf (w * w') = unitOf w * unitOf w') ∧ ∀ (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))), (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) :=
  fun _ _ => ⟨fun _ _ _ => ⟨GmPoints.unitOf_bijective, GmPoints.unitOf_mul⟩,
    fun _ _ _ _ _ _ φ w => GmPoints.unitOf_ptMap φ w⟩
end GlobalTheory
