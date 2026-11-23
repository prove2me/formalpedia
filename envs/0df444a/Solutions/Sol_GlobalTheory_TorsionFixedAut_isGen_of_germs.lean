-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.isGen_of_germs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:14.471412+00:00
-- url     : https://prove2.me/submissions/9e1bdc66-3415-4528-8645-4a6ab7bff6a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (h : ∀ (y : Y) (j j' : K → L.ι), y ∈ LB.wchart L φ j → y ∈ LB.wchart L φ j' →
      gm (𝟙 Y) y (LB.wchart L φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart L φ j') (t.s j')) :
    t.IsGen := fun j j' => unit_ext fun y hy =>
  ((gm_res (𝟙 Y) y _ hy _).trans (h y j j' hy.1 hy.2)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) (gm_res (𝟙 Y) y _ hy _))).symm
end GlobalTheory.TorsionFixedAut
