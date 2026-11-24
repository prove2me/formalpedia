-- Prove2me | solution 1 for GlobalTheory.FunObj.moved_false
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:38.016887+00:00
-- url     : https://prove2.me/submissions/fab90a3e-41af-4404-bcef-d720ee764d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_invT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution (g : G.VertexGroup) (T : G.Args → ℂ) (z : G.Args) : moved G false g T z =
    ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod * T (G.moveArgs .one g z) := by
  simp only [moved, Grid.pathAct, charFactor, ← mul_assoc]
  congr 1
  induction oppositePath G.m with
  | nil => simp
  | cons b γ ih =>
    simp only [List.map_cons, List.prod_cons, ← ih, Grid.edgeFactor, Assignment.read, gdet_invT]
    simp only [Bool.false_eq_true, if_false, _root_.mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
end GlobalTheory.FunObj
