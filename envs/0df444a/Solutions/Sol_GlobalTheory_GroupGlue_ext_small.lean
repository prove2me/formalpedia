-- Prove2me | solution 1 for GlobalTheory.GroupGlue.ext_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:24.274301+00:00
-- url     : https://prove2.me/submissions/47845e51-6fae-42b7-ba25-e2a3b2206985

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
namespace GlobalTheory.GroupGlue
theorem _root_.solution {T Y : Scheme.{0}} (t : T ⟶ X) {p q : T ⟶ Y}
    (h : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ t → g ≫ p = g ≫ q) :
    p = q := by
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ t) p q fun i => ?_
  exact h i _ (pullback.fst t (𝒰.f i)) (pullback.snd t (𝒰.f i)) pullback.condition.symm
end GlobalTheory.GroupGlue
