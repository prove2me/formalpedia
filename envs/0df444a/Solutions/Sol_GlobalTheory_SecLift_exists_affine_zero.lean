-- Prove2me | solution 1 for GlobalTheory.SecLift.exists_affine_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:30.44657+00:00
-- url     : https://prove2.me/submissions/e1b00bd3-5be5-42e0-bec5-f88dc4d24c5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SecLift_exists_open
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution {F : Y ⟶ X} (hF : Topology.IsInducing F) (y : Y) (U : X.Opens)
    (h : (𝟙 Y ≫ F) y ∈ U) (s : Γ(X, U)) (hs : gr (𝟙 Y ≫ F) y U h s = 0) :
    ∃ (V : X.Opens) (hle : V ≤ U), IsAffineOpen V ∧ F y ∈ V ∧ (F.app V).hom (rs X hle s) = 0 := by
  obtain ⟨W, hW, iU, iV, e⟩ := Y.presheaf.germ_eq (U := F ⁻¹ᵁ U) (V := F ⁻¹ᵁ U) y h h
    ((F.app U).hom s) 0 (hs.trans (map_zero _).symm)
  obtain ⟨O, hO, hle⟩ := exists_open hF hW
  obtain ⟨V, hV, hxV, hl⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show F y ∈ O ⊓ U from ⟨hO, h⟩)
  refine ⟨V, hl.trans inf_le_right, hV, hxV, gr_ext fun z hz => ?_⟩
  have hz' : (𝟙 Y : Y ⟶ Y) z ∈ W := hle (hl hz).1
  rw [gr_app, gr_res, map_zero, ← gr_app (𝟙 Y) F z U (hl hz).2, ← gr_res (𝟙 Y) z iU.le hz']
  exact (congrArg (gr (𝟙 Y) z W hz') (e.trans (map_zero _))).trans (map_zero _)
end GlobalTheory.SecLift
