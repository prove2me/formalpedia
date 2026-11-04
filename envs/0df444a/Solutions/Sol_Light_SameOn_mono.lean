-- Prove2me | solution 1 for Light.SameOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:48.811297+00:00
-- url     : https://prove2.me/submissions/6791e8e1-1045-4064-acef-804a1e2ddbe0

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions

set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
namespace Light
namespace SameOn
theorem _root_.solution (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)
end SameOn
end Light
