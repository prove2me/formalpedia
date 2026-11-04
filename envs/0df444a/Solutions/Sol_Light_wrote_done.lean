-- Prove2me | solution 1 for Light.wrote_done
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:51.96585+00:00
-- url     : https://prove2.me/submissions/ede6b45c-abcb-4e9a-9c57-9ffbab7605a0

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
theorem _root_.solution {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]
end Light
