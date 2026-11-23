-- Prove2me | solution 1 for GlobalTheory.GroupGlue.rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:14.448821+00:00
-- url     : https://prove2.me/submissions/86df2b21-9c2d-423b-9122-9b8e7359ec57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts

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
variable [GrpObj G]
namespace GlobalTheory.GroupGlue
theorem _root_.solution (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) {i : 𝒰.I₀} {S : Scheme.{0}} {u : S ⟶ 𝒰.X i}
    {a b : Over.mk u ⟶ H i} {T : Over X} {x y : T ⟶ G} {g : S ⟶ T.left} (hg : u ≫ 𝒰.f i = g ≫ T.hom)
    (ha : a.left ≫ ψ i = g ≫ x.left) (hb : b.left ≫ ψ i = g ≫ y.left) :
    (a * b).left ≫ ψ i = g ≫ (x * y).left := by
  obtain ⟨-, hmul⟩ := h i
  let k : Over.mk (u ≫ 𝒰.f i) ⟶ T := Over.homMk g (by simp [hg])
  have e := hmul (Over.mk u) a b (k ≫ x) (k ≫ y) (by simp [k, ha]) (by simp [k, hb])
  rw [← e, ← MonObj.comp_mul]
  simp [k]
end GlobalTheory.GroupGlue
