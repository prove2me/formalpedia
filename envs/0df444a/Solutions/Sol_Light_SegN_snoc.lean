-- Prove2me | solution 1 for Light.SegN.snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:08.564327+00:00
-- url     : https://prove2.me/submissions/6a23664d-1380-445f-9ceb-a2a9b06041de

import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace SegN
theorem _root_.solution {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)
end SegN
end Light
