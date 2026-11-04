-- Prove2me | solution 1 for Light.Seg.of_sameOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:33:57.017622+00:00
-- url     : https://prove2.me/submissions/36046a64-f5fd-4450-a2d7-ec7e8aee1f50

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
public import Theorems.Thm_Light_Seg_congr

set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace Seg
theorem _root_.solution {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)
end Seg
end Light
