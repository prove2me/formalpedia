-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.linearize_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:44:20.981064+00:00
-- url     : https://prove2.me/submissions/ecb742c3-ecb6-4bbc-8289-c167ca657747

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FreeSpace.lean:L266-L282
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.linearize_unique. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace

-- ---- from OAI.Analysis.LipschitzEquivalence.FreeSpace ----
namespace OAI

universe uM uF

noncomputable section
namespace LipschitzCounterexample

namespace FreeSpace

open scoped NNReal ENNReal

variable (M : Type uM) [MetricSpace M] [Zero M]

variable {M}

section Linearization
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (D : M → F) {K : ℝ≥0} (hD : LipschitzWith K D) (h0 : D 0 = 0)

include hD h0

variable [CompleteSpace F]

theorem linearize_unique (T : Space M →L[ℝ] F) (hT : ∀ x, T (point x) = D x) :
    linearize D = T := by
  apply ContinuousLinearMap.ext
  have heq := dense_combinations.equalizer (linearize D).continuous T.continuous
    (show (linearize D) ∘ Finsupp.linearCombination ℝ point =
      T ∘ Finsupp.linearCombination ℝ point from by
      funext a
      change linearize D (Finsupp.linearCombination ℝ point a) =
        T (Finsupp.linearCombination ℝ point a)
      have h₁ := LinearMap.extendOfNorm_eq (f := Finsupp.linearCombination ℝ D)
        dense_combinations ⟨K, norm_combination_le D hD h0⟩ a
      rw [show linearize D (Finsupp.linearCombination ℝ point a) =
          Finsupp.linearCombination ℝ D a from h₁]
      change _ = T.toLinearMap (Finsupp.linearCombination ℝ point a)
      rw [Finsupp.apply_linearCombination ℝ T.toLinearMap]
      rw [show T.toLinearMap ∘ point = D from funext hT])
  exact congrFun heq

end Linearization

end FreeSpace

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
open scoped NNReal ENNReal


theorem solution.{uM,uF} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.linearize_unique.{uM,uF} := @_root_.OAI.LipschitzCounterexample.FreeSpace.linearize_unique.{uM,uF}
