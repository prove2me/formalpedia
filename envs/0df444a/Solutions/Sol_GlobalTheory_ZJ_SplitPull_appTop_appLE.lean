-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.appTop_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:13.280394+00:00
-- url     : https://prove2.me/submissions/8902cad3-7c36-451e-b6e5-f31055f3379a

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
theorem _root_.solution {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    r.appTop.hom ((φ.appLE V ⊤ k).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ V ⊤ ⊤ k le_top
  rw [← this]
  erw [r.appLE_eq_app]
  rfl
end GlobalTheory.ZJ.SplitPull
