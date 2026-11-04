-- Prove2me | solution 1 for Light.wrote_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:18.791817+00:00
-- url     : https://prove2.me/submissions/eab01abc-29ed-4d30-883d-7b1df2de3925

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Theorems.Thm_Light_wrote_done

set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
variable {dst j : ℕ} {f : ℕ → ℤ}
namespace Light
theorem _root_.solution : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]
end Light
