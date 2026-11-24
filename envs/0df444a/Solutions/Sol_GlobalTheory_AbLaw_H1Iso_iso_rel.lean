-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.iso_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:05.74027+00:00
-- url     : https://prove2.me/submissions/7d762795-1557-49a0-892f-541accb11970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_val_res

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
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.H1Iso
theorem _root_.solution {N M : LB X} (w : LB.Iso M N) (hw : w.IsGen) (i j : N.ι) (k l : M.ι) {W : X.Opens}
    (hi : W ≤ N.U i) (hj : W ≤ N.U j) (hk : W ≤ M.U k) (hl : W ≤ M.U l) :
    rs X (le_inf hi hk : W ≤ N.U i ⊓ M.U k) (wu w i k).val *
        rs X (le_inf hk hl : W ≤ M.U k ⊓ M.U l) (M.g k l).val =
      rs X (le_inf hi hj : W ≤ N.U i ⊓ N.U j) (N.g i j).val *
        rs X (le_inf hj hl : W ≤ N.U j ⊓ M.U l) (wu w j l).val := by
  have h : res (inf_le_left : N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ N.U i ⊓ M.U k) (wu w i k) =
      (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ N.U i ⊓ N.U j) (N.g i j) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ M.U k ⊓ M.U l) (M.g k l))⁻¹) *
      res (inf_le_right : N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ N.U j ⊓ M.U l) (wu w j l) :=
    hw (i, k) (j, l)
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at h
  have h' := congrArg (fun u => rs X (le_inf (le_inf hi hk) (le_inf hj hl) :
    W ≤ N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l)) (Units.val u)) h
  simp only [Units.val_mul, map_mul, val_res, rs_rs] at h'
  exact h'
end GlobalTheory.AbLaw.H1Iso
