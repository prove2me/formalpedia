-- Prove2me | solution 1 for GlobalTheory.PowBasis.comb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:04.568709+00:00
-- url     : https://prove2.me/submissions/2b556e66-57ac-44fb-a861-b2d3dc9452c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsBasisOfFormEq
import Theorems.Thm_GlobalTheory_PowBasis_gs_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowBasis
namespace GlobalTheory.PowBasis
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) (r : Fin m → Γ(Y, ⊤)) :
    (∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (r i) * (b i).f j) ↔
      ∀ y J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (r i) * sval (b i) (𝟙 Y) y J := by
  have key : ∀ (j : K → L.ι) (y : Y) (hy : y ∈ LB.wchart L φ j),
      gs (𝟙 Y) y (LB.wchart L φ j)
        (∑ i, (Y.presheaf.map (homOfLE (le_top : (LB.LinComb L φ ε).U j ≤ ⊤)).op).hom (r i) * (b i).f j :
          Γ(Y, (LB.LinComb L φ ε).U j)) =
      ∑ i, gs (𝟙 Y) y ⊤ (r i) * gs (𝟙 Y) y (LB.wchart L φ j) ((b i).f j) := fun j y hy =>
    (gs_sum (𝟙 Y) y _ hy _).trans (Finset.sum_congr rfl fun i _ =>
      (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg (· * _) (gs_res (𝟙 Y) y le_top hy _)))
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (key _ y (hJ.mem φ (𝟙 Y)))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    refine ((sec_trans s (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans ?_)).trans
      (key j y hy).symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (b i) (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y)), mul_left_comm]
    rfl
end GlobalTheory.PowBasis
