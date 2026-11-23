-- Prove2me | solution 1 for GlobalTheory.GroupGlue.base_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:24.085746+00:00
-- url     : https://prove2.me/submissions/7363d328-6d52-495f-8c6a-7fd9a20048e6

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
namespace GlobalTheory.GroupGlue
theorem _root_.solution (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) {i : 𝒰.I₀} {S : Scheme.{0}}
    {u : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) : u ≫ 𝒰.f i = (a.left ≫ ψ i) ≫ G.hom := by
  have hw := Over.w a
  simp only [Over.mk_hom] at hw
  rw [Category.assoc, (hψ i).w, ← Category.assoc, hw]
end GlobalTheory.GroupGlue
