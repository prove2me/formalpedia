-- Prove2me | solution 1 for MomentComparison.admissible_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:20.281911+00:00
-- url     : https://prove2.me/submissions/2c51bddb-fe7a-412a-a593-7173a9139f05

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_RealHypercontractivity
public import Theorems.Thm_MomentComparison_baseThree

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution :
    {C : ℝ | 0 < C ∧ ∀ (n d : ℕ), 0 < n → 0 < d → ∀ f : Cube n → ℝ,
      HasDegreeLE f d →
        Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ C ^ d * cubeAverage (fun x => |f x|)}.Nonempty :=
  ⟨3, by norm_num, fun _ _ _ _ _ hf => baseThree hf⟩
end MomentComparison
