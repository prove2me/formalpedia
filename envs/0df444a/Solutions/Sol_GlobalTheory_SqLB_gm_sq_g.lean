-- Prove2me | solution 1 for GlobalTheory.SqLB.gm_sq_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:48.290825+00:00
-- url     : https://prove2.me/submissions/9899d45f-ab56-45d5-9139-ee1f39394598

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIso
import Theorems.Thm_GlobalTheory_SqLB_mem_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SqLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.SqLB
theorem _root_.solution (f : Y ⟶ X) (y : Y) {j j' : L.ι} (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y ((sq L).U (fun _ => j) ⊓ (sq L).U (fun _ => j')) ((sq L).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ (2 : ℤ) := by
  refine (gm_linComb L (fun _ => 𝟙 X) (fun _ => 2) f y _ _ (mem_sq hj) (mem_sq hj')).trans ?_
  rw [Fintype.prod_unique, Category.comp_id]
end GlobalTheory.SqLB
