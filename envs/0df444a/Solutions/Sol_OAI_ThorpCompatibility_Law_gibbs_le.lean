-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.gibbs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:20:16.27587+00:00
-- url     : https://prove2.me/submissions/48e9a4a3-cec8-4ec8-af16-39976b3955ec

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/FiniteLaw.lean:L98-L119
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.gibbs_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw

-- ---- from OAI.Probability.ThorpCompatibility.FiniteLaw ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

lemma pointwise_entropy_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) : p - q ≤ p * Real.log (p / q) := by
  by_cases hq0 : q = 0
  · simp [hq0, hzero hq0]
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  calc
    p - q = q * (p / q - 1) := by field_simp
    _ ≤ q * (p / q * Real.log (p / q)) := h
    _ = p * Real.log (p / q) := by field_simp

lemma relativeEntropy_nonneg (P Q : Law α)
    (hzero : ∀ a, Q.mass a = 0 → P.mass a = 0) :
    0 ≤ P.relativeEntropy Q := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    pointwise_entropy_lower (P.nonneg a) (Q.nonneg a) (hzero a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, P.total, Q.total] using h

lemma gibbs_le (P : Law α) (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) (hs : ∀ x, a x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (a x)) -
      (∑ x, P.mass x * Real.log (P.mass x)) ≤ Real.log (∑ x, a x) := by
  have h := P.relativeEntropy_nonneg (tilt a ha hZ) (by
    intro x hx
    exact hs x ((div_eq_zero_iff).mp hx |>.resolve_right hZ.ne'))
  have hterm (x : α) :
      P.mass x * Real.log (P.mass x / (a x / ∑ y, a y)) =
        P.mass x * Real.log (P.mass x) - P.mass x * Real.log (a x) +
          P.mass x * Real.log (∑ y, a y) := by
    by_cases hp : P.mass x = 0
    · simp [hp]
    have hx : a x ≠ 0 := fun hx => hp (hs x hx)
    rw [Real.log_div hp (div_ne_zero hx hZ.ne'), Real.log_div hx hZ.ne']
    ring
  simp only [relativeEntropy, tilt] at h
  simp_rw [hterm] at h
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, P.total,
    one_mul] at h
  unfold mean
  linarith

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

theorem solution (P : Law α) (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) (hs : ∀ x, a x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (a x)) -
      (∑ x, P.mass x * Real.log (P.mass x)) ≤ Real.log (∑ x, a x) := by
  first
    | exact OAI.ThorpCompatibility.Law.gibbs_le P a ha hZ hs
    | exact OAI.ThorpCompatibility.Law.gibbs_le
    | (apply OAI.ThorpCompatibility.Law.gibbs_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.gibbs_le <;> assumption)
