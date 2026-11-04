-- Prove2me | solution 1 for Light.SameOn.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:47.740451+00:00
-- url     : https://prove2.me/submissions/9a0fb3c3-bfb4-4510-b74e-55d9bf0a233f

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
theorem _root_.solution : SameOn K μ μ := fun _ _ => rfl
end SameOn
end Light
