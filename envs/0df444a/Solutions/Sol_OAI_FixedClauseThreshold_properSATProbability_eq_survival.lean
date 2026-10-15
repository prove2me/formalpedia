-- Prove2me | solution 1 for OAI.FixedClauseThreshold.properSATProbability_eq_survival
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:24:44.632635+00:00
-- url     : https://prove2.me/submissions/53348730-3822-4b9e-bd16-6b7f44fe4f53

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/ClauseProcess.lean:L182-L194
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.properSATProbability_eq_survival. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.ClauseProcess ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem properSATProbability_eq_survival (n k m : ℕ) :
    properSATProbability n k m = survival k m (Finset.univ : Finset (Assignment n)) := by
  rw [survival_eq_mean]
  change uniformProbability (fun F : Formula n k m => Satisfiable F) = _
  rw [uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  simp only [Finset.nonempty_iff_ne_empty]
  apply propext
  rw [← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty, Satisfiable, Satisfies]

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.properSATProbability_eq_survival := @_root_.OAI.FixedClauseThreshold.properSATProbability_eq_survival
