-- Prove2me | solution 1 for GlobalTheory.ExpCmp.eq_unitMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:06:49.992861+00:00
-- url     : https://prove2.me/submissions/a22d180d-5509-43a9-b9a3-1e4f659528d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd
import Theorems.Thm_GlobalTheory_UnitSec_snd_unit_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
namespace GlobalTheory.ExpCmp
theorem _root_.solution {S S' Z : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left)
    {r' : Z ⟶ (𝟙_ (Over S') ⊗ G').left} {r : Z ⟶ (𝟙_ (Over S) ⊗ G).left}
    (h : r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F) : r = r' ≫ unitMap F := by
  rw [unitMap, ← Category.assoc _ F, ← Category.assoc r', ← h, Category.assoc, snd_unit_inv, Category.comp_id]
end GlobalTheory.ExpCmp
