-- Prove2me | solution 1 for GlobalTheory.TauBalPull.push_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:37.370818+00:00
-- url     : https://prove2.me/submissions/68e8c26e-3fad-47dc-8797-78193fb2efd4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.TauBalPull
theorem _root_.solution (hD : IsPullDeg φ D D') {f : D.P.A ⟶ D.P.A} {f' : D'.P.A ⟶ D'.P.A}
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f) {T : Over (Sp R')} (x : T ⟶ D'.P.A) :
    pushPt (pull_grp hD).1.w (x ≫ f') = pushPt (pull_grp hD).1.w x ≫ f := by
  refine Over.OverMorphism.ext ?_
  have h₁ : f'.left ≫ hD.e.hom.left = hD.e.hom.left ≫ ((Over.pullback (specOf φ)).map f).left :=
    congrArg (fun q => q.left) hf
  have h₂ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
  show (x.left ≫ f'.left) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
    (x.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left
  rw [Category.assoc, ← Category.assoc f'.left, h₁]
  simp only [Category.assoc]
  exact congrArg (fun q => x.left ≫ hD.e.hom.left ≫ q) h₂
end GlobalTheory.TauBalPull
