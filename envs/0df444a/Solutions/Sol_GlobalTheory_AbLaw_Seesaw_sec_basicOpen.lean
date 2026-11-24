-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.sec_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:26.891235+00:00
-- url     : https://prove2.me/submissions/3e88f9b8-38ad-4baf-b4b9-553ea5868501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_mem_basicOpen_rs
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_mem_of_isUnit

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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution {N : LB Y} (s : LB.Sec N) {i j : N.ι} {y : Y} (hi : y ∈ N.U i)
    (h : y ∈ Y.basicOpen (s.f j)) : y ∈ Y.basicOpen (s.f i) := by
  have hj : y ∈ N.U j := Y.basicOpen_le _ h
  have hij : y ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  rw [← mem_basicOpen_rs inf_le_left _ hij, s.compat i j, Scheme.basicOpen_mul]
  exact ⟨mem_of_isUnit (Units.isUnit _) hij, (mem_basicOpen_rs inf_le_right _ hij).2 h⟩
end GlobalTheory.AbLaw.Seesaw
