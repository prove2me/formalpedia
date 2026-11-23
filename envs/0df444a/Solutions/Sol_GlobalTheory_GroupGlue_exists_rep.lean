-- Prove2me | solution 1 for GlobalTheory.GroupGlue.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:44.89491+00:00
-- url     : https://prove2.me/submissions/4267e7a5-c5e0-4feb-95d4-b20269984b73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_exists_lift

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
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]
omit [∀ i, GrpObj (H i)]
namespace GlobalTheory.GroupGlue
theorem _root_.solution (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) {i : 𝒰.I₀} {S : Scheme.{0}}
    {u : S ⟶ 𝒰.X i} {T : Over X} {g : S ⟶ T.left} (h : u ≫ 𝒰.f i = g ≫ T.hom) (x : T ⟶ G) :
    ∃ a : Over.mk u ⟶ H i, a.left ≫ ψ i = g ≫ x.left := exists_lift hψ i u (g ≫ x.left) (by simp [h])
end GlobalTheory.GroupGlue
