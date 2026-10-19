-- Prove2me | solution 1 for OAI.BackwardIntertwiners.DiscreteConvex.slopes_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:40:12.945186+00:00
-- url     : https://prove2.me/submissions/2b423a22-c02c-457b-9e9d-cbe680a3d255

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean:L200-L215
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.DiscreteConvex.slopes_tendsto. The node keeps its source
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

lemma step (h : DiscreteConvex F) (n : ℕ) :
    F (n+1) - F n ≤ F (n+2) - F (n+1) := by
  exact h (Nat.le_succ n)

lemma sub_zero_le (h : DiscreteConvex F) (n : ℕ) :
    F n - F 0 ≤ (n : ℝ) * (F (n+1) - F n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hs := h.step n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith

end DiscreteConvex

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma slopes_tendsto (h : DiscreteConvex F) (h0 : F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ F n) :
    Tendsto (fun n => F (n+1) - F n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn : ∀ᶠ n : ℕ in atTop, b / δ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      (eventually_ge_atTop _)
  filter_upwards [hq, hn, eventually_ge_atTop 1] with n hqn hbn hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs := h.sub_zero_le n
  rw [h0, sub_zero] at hs
  have hb : b ≤ δ * n := (div_le_iff₀ hδ).mp hbn |>.trans_eq (mul_comm _ _)
  have hd : δ * n ≤ F (n+1) - F n := by nlinarith
  exact hb.trans hd

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners OAI.BackwardIntertwiners.DiscreteConvex
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.DiscreteConvex.slopes_tendsto := @_root_.OAI.BackwardIntertwiners.DiscreteConvex.slopes_tendsto
