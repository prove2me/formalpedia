-- Prove2me | solution 1 for Light.SameOutside2.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:34:38.07998+00:00
-- url     : https://prove2.me/submissions/bf08635b-00c5-4bf5-8393-1c42bf120b5b

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
public import Theorems.Thm_Light_SameOutside_refl
public import Theorems.Thm_Light_SameOn_refl


set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace SameOutside2
theorem _root_.solution {m : ℕ} : SameOutside2 μ μ a n b m := SameOn.refl
end SameOutside2
end Light
