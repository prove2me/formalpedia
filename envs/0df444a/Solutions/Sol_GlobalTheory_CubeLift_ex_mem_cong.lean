-- Prove2me | solution 1 for GlobalTheory.CubeLift.ex_mem_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:45.644702+00:00
-- url     : https://prove2.me/submissions/039328f8-8f5b-439a-a02a-12191305c11d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Theorems.Thm_GlobalTheory_CubeLift_ev_bcMap
import Theorems.Thm_GlobalTheory_CubeLift_ev_injective
import Theorems.Thm_GlobalTheory_CubeLift_mem_cong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.CubeLift
theorem _root_.solution (J : Ideal A) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex u ∈ cong J ↔ app (bcMap (red J) X) u = 1 := by
  have key : ev (𝟙 _) ((bcMap (red J) X).appTop.hom u.val) = rd J (ev (𝟙 _) u.val) := by
    rw [ev_bcMap, Category.id_comp,
      show red J = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 _ from (Category.comp_id _).symm,
      SplitTorus.ev_comp]
    rfl
  rw [mem_cong, Units.ext_iff, Units.val_one]
  change rd J (ev (𝟙 _) u.val) = 1 ↔ (bcMap (red J) X).appTop.hom u.val = 1
  constructor
  · intro h
    apply ev_injective
    rw [key, h, map_one]
  · intro h
    rw [← key, h, map_one]
end GlobalTheory.CubeLift
