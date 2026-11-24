-- Prove2me | solution 1 for MomentComparison.lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:32.530803+00:00
-- url     : https://prove2.me/submissions/4d1ea66f-03a7-40b2-8d15-b8e71cb847f1

module
public import Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_FiniteFourth
public import Definitions.Def_MomentComparison_RealHypercontractivity
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Lower
public import Theorems.Thm_MomentComparison_lowerBound_of_admissible
public import Theorems.Thm_MomentComparison_admissible_nonempty


set_option autoImplicit true
@[expose] public section
public section
open Filter Finset
open scoped Topology
open MomentComparison
namespace MomentComparison
theorem _root_.solution : Real.sqrt 3 ≤ Cstar := by
  unfold Cstar
  refine le_csInf admissible_nonempty ?_
  rintro C ⟨hC, h⟩
  exact lowerBound_of_admissible hC h
end MomentComparison
