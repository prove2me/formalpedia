-- Prove2me | solution 1 for Light.SegN.drop_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:34:39.192074+00:00
-- url     : https://prove2.me/submissions/0d2042ea-2fef-46d3-bc6d-2a5114f868c8

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace SegN
theorem _root_.solution {l : List ℕ} (h : SegN μ a l) (lo w : ℕ) :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa only [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w
end SegN
end Light
