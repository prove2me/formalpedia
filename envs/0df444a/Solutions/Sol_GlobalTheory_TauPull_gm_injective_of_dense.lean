-- Prove2me | solution 1 for GlobalTheory.TauPull.gm_injective_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:19.572107+00:00
-- url     : https://prove2.me/submissions/1b2d9915-ef09-4bd2-8851-54cba5b5fdf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


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
open GlobalTheory.TauPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.TauPull
theorem _root_.solution {Y Z : Scheme.{0}} [IsReduced Y] (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V) (V : Y.Opens) (hV : h z ∈ V) :
    Function.Injective (gm h z V) := by
  intro a b hab
  apply Units.ext
  have e := congrArg Units.val hab
  rw [gm_val h z V hV, gm_val h z V hV, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hm : z ∈ h ⁻¹ᵁ Y.basicOpen (a.val - b.val) :=
    hd _ (by
      by_contra hn
      exact hne (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _ |>.1 hn))
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ z hV, e] at hm
  exact not_isUnit_zero hm
end GlobalTheory.TauPull
