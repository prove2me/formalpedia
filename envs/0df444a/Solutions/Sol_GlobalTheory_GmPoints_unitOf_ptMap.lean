-- Prove2me | solution 1 for GlobalTheory.GmPoints.unitOf_ptMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:40.05867+00:00
-- url     : https://prove2.me/submissions/9c111acd-2290-43c3-bc47-5f25e66166ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_val

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
open GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
namespace GlobalTheory.GmPoints
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R')
    (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) := by
  rw [unitOf_val, unitOf_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of R' => g.hom _)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))
end GlobalTheory.GmPoints
