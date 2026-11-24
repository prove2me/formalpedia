-- Prove2me | solution 1 for MomentComparison.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:27:32.781821+00:00
-- url     : https://prove2.me/submissions/b43a97b7-984d-4ca8-ba1d-70d76536b5d3

module
public import Definitions.Def_MomentComparison_Lower
public import Definitions.Def_MomentComparison_Upper
public import Definitions.Def_MomentComparison_Solution
public import Theorems.Thm_MomentComparison_cstar_le_upperBase
public import Theorems.Thm_MomentComparison_lowerBound


set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution : Real.sqrt 3 ≤ Cstar ∧ Cstar ≤ upperBase := by
  exact ⟨lowerBound, cstar_le_upperBase⟩
end MomentComparison
