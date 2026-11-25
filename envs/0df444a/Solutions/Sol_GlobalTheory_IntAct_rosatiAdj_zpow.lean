-- Prove2me | solution 1 for GlobalTheory.IntAct.rosatiAdj_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:58.027172+00:00
-- url     : https://prove2.me/submissions/7e9a5ae8-ce40-4339-92f9-bb14ed15a0f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
import Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_one
import Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_id
import Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_inv
import Theorems.Thm_GlobalTheory_rosatiAdj_mul


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
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.IntAct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
namespace GlobalTheory.IntAct
theorem _root_.solution (M : RigLB A) (c : CubicalStr A M) (hs : Out.Sym A M.L) (a : ℤ) :
    RosatiAdj A M.L ((𝟙 A) ^ a) ((𝟙 A) ^ a) := by
  induction a using Int.induction_on with
  | zero => rw [zpow_zero]; exact rosatiAdj_one M.isLB
  | succ n ih => rw [zpow_add_one]; exact rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_id M.isLB)
  | pred n ih => rw [zpow_sub_one]; exact rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_inv M.isLB hs)
end GlobalTheory.IntAct
