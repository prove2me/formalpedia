-- Prove2me | solution 1 for GlobalTheory.AbLaw.TwExtend.basicOpen_rs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:18:11.851803+00:00
-- url     : https://prove2.me/submissions/0c0d0844-177d-4d6b-a3f7-605e2c790e55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.TwExtend
variable {Y : Scheme.{0}}
namespace GlobalTheory.AbLaw.TwExtend
theorem _root_.solution {L : LB Y} (s : LB.Sec L) (k : L.ι) {W : Y.Opens} (h : W ≤ L.U k) :
    Y.basicOpen (rs Y h (s.f k)) = nonzeroLocus s ⊓ W := by
  apply le_antisymm
  · have hb : Y.basicOpen (rs Y h (s.f k)) = W ⊓ Y.basicOpen (s.f k) := Y.basicOpen_res _ _
    rw [hb]
    exact le_inf (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) k)) inf_le_left
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s k
      (inf_le_right.trans h : nonzeroLocus s ⊓ W ≤ L.U k) inf_le_left
    rw [← rs_rs h inf_le_right] at hu
    have hb : Y.basicOpen (rs Y (inf_le_right : nonzeroLocus s ⊓ W ≤ W) (rs Y h (s.f k))) =
      (nonzeroLocus s ⊓ W) ⊓ Y.basicOpen (rs Y h (s.f k)) := Y.basicOpen_res _ _
    rw [Y.basicOpen_of_isUnit hu] at hb
    exact hb.le.trans inf_le_right
end GlobalTheory.AbLaw.TwExtend
