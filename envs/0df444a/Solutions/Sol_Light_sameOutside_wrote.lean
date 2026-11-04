-- Prove2me | solution 1 for Light.sameOutside_wrote
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:20.982852+00:00
-- url     : https://prove2.me/submissions/884d2fc9-50b6-4047-99f2-b2f1574c8a39

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Theorems.Thm_Light_wrote_rest

set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
variable {dst j : ℕ} {f : ℕ → ℤ}
namespace Light
theorem _root_.solution {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)
end Light
