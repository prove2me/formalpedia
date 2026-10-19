-- Prove2me | solution 1 for OAI.BackwardIntertwiners.no_both_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:49:46.628664+00:00
-- url     : https://prove2.me/submissions/973674d5-60fb-4d7c-a47f-bb5d0d04cc51

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean:L70-L93
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.no_both_unbounded. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Theorems.Thm_OAI_BackwardIntertwiners_CoefficientEnvelope_properties
import Theorems.Thm_OAI_BackwardIntertwiners_no_correlation_of_envelopes

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

theorem no_both_unbounded {P Q : ℕ → ℝ} {b c : ℤ → ℂ}
    (hb : EnvelopeBounds P Q b c) (hP : DiscreteConvex P) (hQ : DiscreteConvex Q)
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0) {lam δ : ℝ}
    (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^2 ≤ P n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^2 ≤ Q n)
    (hbu : ∀ n : ℕ, ∃ k, n < k ∧ b (k : ℤ) ≠ 0)
    (hcu : ∀ n : ℕ, ∃ k, n < k ∧ c (-(k : ℤ)) ≠ 0)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by
  obtain ⟨hA0, hA, hPA, hcA, hcontactA⟩ :=
    CoefficientEnvelope.properties hcu hP hP0 hb.c_neg
  obtain ⟨hB0, hB, hQB, hbB, hcontactB⟩ :=
    CoefficientEnvelope.properties hbu hQ hQ0 hb.b_pos
  let A := coefficientEnvelope (fun n => c (-(n : ℤ)))
  let B := coefficientEnvelope (fun n => b (n : ℤ))
  apply no_correlation_of_envelopes (A := A) (B := B) (b := b) (c := c)
    ?_ hA hB hA0 hB0 hlam hδ ?_ ?_ hcontactA hcontactB hz
  · refine ⟨hbB, ?_, ?_, hcA⟩
    · intro n
      exact (hb.b_neg n).trans (Real.exp_le_exp.mpr (hPA n))
    · intro n
      exact (hb.c_pos n).trans (Real.exp_le_exp.mpr (hQB n))
  · filter_upwards [hqp] with n hn using hn.trans (hPA n)
  · filter_upwards [hqq] with n hn using hn.trans (hQB n)

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.no_both_unbounded := @_root_.OAI.BackwardIntertwiners.no_both_unbounded
