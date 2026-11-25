-- Prove2me | solution 1 for GlobalTheory.ObjComp.sec_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:54:04.766057+00:00
-- url     : https://prove2.me/submissions/c24aeb15-3430-4940-a2e8-25e9362ffd1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ObjMapIdCompCancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ObjComp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H}
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
namespace GlobalTheory.ObjComp
theorem _root_.solution {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (hp : IsPullback φ G'.hom G.hom f) (w : φ' ≫ G'.hom = G''.hom ≫ f')
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (hx' : x' ≫ G'.hom = 𝟙 _) (hx'' : x'' ≫ G''.hom = 𝟙 _)
    (h : x' ≫ φ = f ≫ x) (h'' : x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x) : x'' ≫ φ' = f' ≫ x' := by
  apply hp.hom_ext
  · rw [Category.assoc, h'', Category.assoc, Category.assoc, h]
  · rw [Category.assoc, w, ← Category.assoc, hx'', Category.assoc, hx']; simp
end GlobalTheory.ObjComp
