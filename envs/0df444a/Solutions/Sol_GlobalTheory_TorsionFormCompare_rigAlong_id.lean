-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.rigAlong_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:34.784355+00:00
-- url     : https://prove2.me/submissions/a7b7fb15-ee7e-4dd7-bf69-6f4237eda0bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_idIso_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_idIso_maps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isoPullId_maps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isoPullId_pgen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    RigAlong (𝟙 G) L L (isoPullId (idIso L.L) rfl) := by
  have he : eSec G ≫ (𝟙 G : G ⟶ G).left = 𝟙 _ ≫ eSec G := by simp
  exact ⟨(isGen_iff _).2 (isoPullId_pgen (idIso_isGen L.isLB) rfl),
    (maps_iff _ _ (fun _ => eSec G) _ L.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L) (fun _ => rfl)).1
      (isoPullId_maps (idIso_maps L) rfl rfl he)⟩
end GlobalTheory.TorsionFormCompare
