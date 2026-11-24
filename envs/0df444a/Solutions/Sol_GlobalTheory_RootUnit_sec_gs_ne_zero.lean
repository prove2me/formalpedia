-- Prove2me | solution 1 for GlobalTheory.RootUnit.sec_gs_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:24:29.100915+00:00
-- url     : https://prove2.me/submissions/b7f24e45-f4df-4ad7-910d-d65fc691ae49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Theorems.Thm_GlobalTheory_RootUnit_gs_id
import Theorems.Thm_GlobalTheory_RootUnit_gs_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RootUnit
open TopologicalSpace
namespace GlobalTheory.RootUnit
theorem _root_.solution {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∃ j, s.f j ≠ 0) (y : Y) (i : K → L.ι)
    (hy : y ∈ LB.wchart L φ i) : gs (𝟙 Y) y (LB.wchart L φ i) (s.f i) ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (LB.wchart L φ j : Set Y).Nonempty := by
    by_contra hn
    exact hj (fn_ext (V := LB.wchart L φ j) fun x hx => absurd ⟨x, hx⟩ hn)
  obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ i).isOpen hne ⟨y, hy⟩
  refine gs_ne_zero y _ hy fun e => gs_ne_zero z _ hz hj ?_
  rw [sec_trans s (𝟙 Y) z hz hz', e, gs_id z _ hz', map_zero, mul_zero]
end GlobalTheory.RootUnit
