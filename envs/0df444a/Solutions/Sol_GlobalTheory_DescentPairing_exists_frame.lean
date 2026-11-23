-- Prove2me | solution 1 for GlobalTheory.DescentPairing.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:21.005845+00:00
-- url     : https://prove2.me/submissions/460c15c0-1e3a-44dd-87a1-d3c73980d5af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
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
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DescentPairing
namespace GlobalTheory.DescentPairing
theorem _root_.solution {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y₀ : Y) (hY : ∀ y : Y, y = y₀) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen := by
  choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y₀)
  have m₀ : ∀ y : Y, y ∈ LB.wchart M φ (fun k => I (φ k)) := fun y => by
    rw [hY y]; exact Set.mem_iInter.2 fun k => hI _
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ (fun k => I (φ k)) := fun j y hy => ⟨hy, m₀ y⟩
  have v : ∀ j (y : Y), y ∈ LB.wchart M φ j →
      gm (𝟙 Y) y _ (res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))) = trF φ ε (𝟙 Y) y j (fun k => I (φ k)) :=
    fun j y hy => (gm_res (𝟙 Y) y (le j) hy _).trans (gm_linComb M φ ε (𝟙 Y) y j _ hy (m₀ y))
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j y hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (v j' y hy.2))).trans ?_)
  exact trF_trans hM φ ε (𝟙 Y) y hy.1 hy.2 (m₀ y)
end GlobalTheory.DescentPairing
