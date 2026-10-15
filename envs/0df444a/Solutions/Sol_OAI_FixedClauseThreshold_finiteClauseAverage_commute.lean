-- Prove2me | solution 1 for OAI.FixedClauseThreshold.finiteClauseAverage_commute
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:40:16.776112+00:00
-- url     : https://prove2.me/submissions/97338238-3615-4290-835f-7eca6a3c1752

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Interpolation.lean:L57-L71
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.finiteClauseAverage_commute. The node keeps its source
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

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem finiteClauseAverage_commute {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop) :
    Function.Commute (finiteClauseAverage satC) (finiteClauseAverage satD) := by
  intro f
  funext S
  unfold finiteClauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro d
  apply uniformMean_congr
  intro c
  congr 1
  ext σ
  simp only [Finset.mem_filter]
  tauto

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.finiteClauseAverage_commute := @_root_.OAI.FixedClauseThreshold.finiteClauseAverage_commute
