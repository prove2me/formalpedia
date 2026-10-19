-- Prove2me | solution 1 for OAI.BackwardIntertwiners.DiscreteConvex.tail_term_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:43:21.371985+00:00
-- url     : https://prove2.me/submissions/56a9680d-dc94-4d9c-847e-67a2d23b5214

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean:L352-L368
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.DiscreteConvex.tail_term_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvexEnvelope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma increment_lower (h : DiscreteConvex F) (q k : ℕ) :
    (k : ℝ) * (F (q+1) - F q) ≤ F (q+k) - F q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (Nat.le_add_right q k)
    have e : q + (k+1) = q+k+1 := by omega
    rw [e]
    push_cast
    nlinarith

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma tail_term_tendsto (h : DiscreteConvex F)
    (hs : Tendsto (fun n => F (n+1) - F n) atTop atTop) (k : ℕ) :
    Tendsto (fun q => normalizedTailTerm F q k) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot.2
  intro b
  have hsl := hs (eventually_ge_atTop (max 0 (F (k+1) - b)))
  filter_upwards [hsl] with q hq
  have hs0 : 0 ≤ F (q+1) - F q := (le_max_left _ _).trans hq
  have hsb : F (k+1) - b ≤ F (q+1) - F q := (le_max_right _ _).trans hq
  have hi := h.increment_lower q (k+1)
  have e : q+(k+1) = q+k+1 := by omega
  rw [e] at hi
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast at hi
  change F (k+1) + F q - F (q+k+1) ≤ b
  nlinarith

end DiscreteConvex

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners OAI.BackwardIntertwiners.DiscreteConvex
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.DiscreteConvex.tail_term_tendsto := @_root_.OAI.BackwardIntertwiners.DiscreteConvex.tail_term_tendsto
