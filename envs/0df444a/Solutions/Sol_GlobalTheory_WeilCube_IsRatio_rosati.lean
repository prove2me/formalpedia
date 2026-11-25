-- Prove2me | solution 1 for GlobalTheory.WeilCube.IsRatio.rosati
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:48.821573+00:00
-- url     : https://prove2.me/submissions/cb048bcf-9171-44b5-8018-b09169dec8c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_GlobalTheory_WeilCube_cubN_rosati

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)
namespace GlobalTheory.WeilCube
namespace IsRatio
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A Lr.L f g) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1)
    {e : Γ(T.left, ⊤)ˣ} (he : IsRatio c k (x ≫ f) y e) : IsRatio c k x (y ≫ g) e := by
  intro T' ρ z J hJ
  obtain ⟨u, h₁, h₂⟩ := cubN_rosati c hG hA f g h (x := ρ ≫ x) (y := ρ ≫ y)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) z J hJ
  have := he T' ρ z J hJ
  rw [← Category.assoc] at this ⊢
  rw [h₁, h₂, ← this, _root_.mul_assoc]
end IsRatio
end GlobalTheory.WeilCube
