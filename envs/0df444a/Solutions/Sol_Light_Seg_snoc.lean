-- Prove2me | solution 1 for Light.Seg.snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:55.215488+00:00
-- url     : https://prove2.me/submissions/7b4794a2-54ea-4d0e-96f9-47b3dc8c355e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Theorems.Thm_Light_Seg_update_out
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace Seg
theorem _root_.solution (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩
end Seg
end Light
