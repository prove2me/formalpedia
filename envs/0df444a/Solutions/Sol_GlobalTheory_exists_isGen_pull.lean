-- Prove2me | solution 1 for GlobalTheory.exists_isGen_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:20.483278+00:00
-- url     : https://prove2.me/submissions/a7892870-81b6-46f3-9914-3fd31b3210ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsGenOfInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (M : LB X) (v : LB.Gen M) (hv : v.IsGen) (f : Y ⟶ X) :
    ∃ c : LB.Gen (M.pull f), c.IsGen := by
  have le : ∀ J : PUnit → M.ι, (M.pull f).U J ≤ f ⁻¹ᵁ M.U (J PUnit.unit) := fun J y hy => mem_pull.1 hy
  refine ⟨⟨fun J => res (le J) (pullU f _ (v.s (J PUnit.unit)))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J : PUnit → M.ι, y ∈ (M.pull f).U J →
      gm (𝟙 Y) y _ (res (le J) (pullU f _ (v.s (J PUnit.unit)))) =
        gm (𝟙 Y ≫ f) y _ (v.s (J PUnit.unit)) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gm (𝟙 Y ≫ f) y _) (hv (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))
end GlobalTheory
