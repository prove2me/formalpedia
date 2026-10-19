-- Prove2me | solution 1 for OAI.BackwardIntertwiners.stepRatio_summable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:53:06.111067+00:00
-- url     : https://prove2.me/submissions/283f6dbf-bd10-44a2-ae15-a8880d47df63

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean:L211-L235
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.stepRatio_summable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

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

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma summable_exp_neg_slope (h : DiscreteConvex F) (h0 : F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ F n) :
    Summable (fun n => Real.exp (-(F (n+1) - F n))) := by
  have hgeo : Summable (fun n : ℕ => Real.exp (-δ) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using hδ)
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hq, eventually_ge_atTop 1] with n hqn hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs := h.sub_zero_le n
  rw [h0, sub_zero] at hs
  have hd : δ * n ≤ F (n+1) - F n := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith)

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.CoefficientSupport ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

end CoefficientEnvelope

lemma stepRatio_summable {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (hw0 : w 0 = 1)
    (hP : DiscreteConvex (negativeLog w)) (hQ : DiscreteConvex (positiveLog w))
    {δ : ℝ} (hδ : 0 < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ negativeLog w n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n) :
    Summable (stepRatio w) := by
  have hP0 : negativeLog w 0 = 0 := by simp [negativeLog, hw0]
  have hQ0 : positiveLog w 0 = 0 := by simp [positiveLog, hw0]
  have hsP := hP.summable_exp_neg_slope hP0 hδ hqp
  have hsQ := hQ.summable_exp_neg_slope hQ0 hδ hqq
  apply Summable.of_nat_of_neg_add_one
  · apply hsQ.congr
    intro n
    unfold stepRatio positiveLog
    have he : -(-Real.log (w (n+1)) - -Real.log (w n)) =
        Real.log (w (n+1)) - Real.log (w n) := by ring
    push_cast
    rw [he, Real.exp_sub, Real.exp_log (hw _), Real.exp_log (hw _)]
  · apply hsP.congr
    intro n
    unfold stepRatio negativeLog
    have hi : -((n:ℤ)+1)+1 = -(n:ℤ) := by omega
    rw [hi]
    push_cast
    rw [neg_sub, Real.exp_sub, Real.exp_log (hw _), Real.exp_log (hw _)]

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.stepRatio_summable := @_root_.OAI.BackwardIntertwiners.stepRatio_summable
