-- Prove2me | solution 1 for GlobalTheory.ObjComp.objMap_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:04.449015+00:00
-- url     : https://prove2.me/submissions/7cacf78d-ec64-4972-8f37-6d6665f939fd

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
import Theorems.Thm_GlobalTheory_ObjComp_sec_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabCancel


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
theorem _root_.solution (m : ObjMap o' o f) (n : ObjMap o'' o (f' ≫ f)) :
    ∃ m' : ObjMap o'' o' f', n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨m', hn⟩ := sabCancel pullCubCancel E H S S' S'' o.t o'.t o''.t f f' m.toSABMap n.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨m', fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.eta a)) (Over.w (o''.eta a)) (m.eta a)
      (by rw [← hn']; exact n.eta a),
    fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.etaA a)) (Over.w (o''.etaA a)) (m.etaA a)
      (by rw [← hn']; exact n.etaA a)⟩, hn⟩
end GlobalTheory.ObjComp
