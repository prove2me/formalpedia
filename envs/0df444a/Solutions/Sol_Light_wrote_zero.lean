-- Prove2me | solution 1 for Light.wrote_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:50.823205+00:00
-- url     : https://prove2.me/submissions/8e6baea0-a655-4224-9fd9-e6a9b46f2a66

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions

set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
variable {dst j : ℕ} {f : ℕ → ℤ}
namespace Light
theorem _root_.solution : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]
end Light
