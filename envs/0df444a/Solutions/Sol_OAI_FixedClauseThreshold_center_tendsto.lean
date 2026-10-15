-- Prove2me | solution 1 for OAI.FixedClauseThreshold.center_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T06:01:11.294821+00:00
-- url     : https://prove2.me/submissions/7e39952e-9d66-4795-8138-f013a562e7b8

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Main.lean:L21-L35
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.center_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Definitions.Def_OAI_Probability_RandomSAT_Convergence
import Definitions.Def_OAI_Probability_RandomSAT_Main
import Theorems.Thm_OAI_FixedClauseThreshold_center_bounds_eventually
import Theorems.Thm_OAI_FixedClauseThreshold_center_comparisons
import Theorems.Thm_OAI_FixedClauseThreshold_summable_min_convergence

-- ---- from OAI.Probability.RandomSAT.Concentration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem delta_pos {k : ℕ} (hk : 3 ≤ k) : 0 < delta k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold delta
  exact div_pos (by linarith) (by positivity)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Main ----
namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem center_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => center n k) Filter.atTop (nhds (limitingCenter k)) := by
  have hb := center_bounds_eventually k hk
  have hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n : ℕ => center n k) :=
    Filter.isBoundedUnder_of_eventually_le (hb.mono (fun _ h => h.2))
  have hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n : ℕ => center n k) :=
    Filter.isBoundedUnder_of_eventually_ge (hb.mono (fun _ h => h.1))
  apply summable_min_convergence (fun n => center n k) (by norm_num : (0 : ℝ) ≤ 4)
    (delta_pos hk) hUpper hLower
  obtain ⟨N, hadd, hnext⟩ := center_comparisons k hk
  refine ⟨N, ?_, ?_⟩
  · intro r hr s hs
    simpa only [densityWindow, Nat.cast_min] using hadd r hr s hs
  · intro s hs
    exact hnext s hs

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.center_tendsto := @_root_.OAI.FixedClauseThreshold.center_tendsto
