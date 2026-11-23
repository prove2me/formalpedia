-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.gm_twistGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:13.266173+00:00
-- url     : https://prove2.me/submissions/65ebe281-5f5d-478c-b611-b097989bc838

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
variable {σ : X ⟶ X} (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1]))
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : K × Fin 2 → L.ι)
    (hj : r z ∈ LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j) :
    gm r z (LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j) ((twistGen c φ ε).s j) =
      ∏ k, gm r z (LB.wchart L (fun b => φ k ≫ ![σ, 𝟙 X] b) (fun b => j (k, b)))
        ((LB.pullGen L _ _ c (φ k)).s (fun b => j (k, b))) ^ (-ε k) :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
    (congrArg (· ^ (-ε k)) (gm_res r z _ hj _)))
end GlobalTheory.TorsionFixedAut
