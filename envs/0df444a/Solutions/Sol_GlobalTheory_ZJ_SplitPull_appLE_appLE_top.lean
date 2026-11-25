-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.appLE_appLE_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:33.237241+00:00
-- url     : https://prove2.me/submissions/de1c8c6a-1e85-4af0-9078-d5119b670de7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU
namespace GlobalTheory.ZJ.SplitPull
theorem _root_.solution {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : r ≫ φ = s) (V : B.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(C, ⊤)) :
    (r.appLE V ⊤ k).hom ((φ.appLE ⊤ V le_top).hom u) = s.appTop.hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ ⊤ V ⊤ le_top k
  erw [(r ≫ φ).appLE_eq_app] at this
  exact congrArg (fun q => q.hom u) this
end GlobalTheory.ZJ.SplitPull
