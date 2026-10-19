-- Prove2me | solution 1 for OAI.Problem313.weighted_fourth_moment_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:03:22.308964+00:00
-- url     : https://prove2.me/submissions/daed885d-c558-4a76-9ac5-f09e4cba4d64

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/HypercontractiveTensor.lean:L24-L52
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.weighted_fourth_moment_add_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

-- ---- from OAI.Combinatorics.SharpThreshold.HypercontractiveTensor ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Weighted Cauchy--Schwarz in a form useful for finite product measures. -/
theorem weighted_cauchy_schwarz_sq {α : Type u} (s : Finset α)
    (w u v : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x * u x * v x) ^ 2 ≤
      (∑ x ∈ s, w x * (u x) ^ 2) * (∑ x ∈ s, w x * (v x) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    exact le_of_eq (by ring)

/-- The root-free Minkowski step in tensorization of the fourth moment. -/
theorem weighted_fourth_moment_add_sq {α : Type u} (s : Finset α)
    (w A B : α → ℝ) (a b : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : (∑ x ∈ s, w x * (A x) ^ 4) ≤ a ^ 2)
    (hB : (∑ x ∈ s, w x * (B x) ^ 4) ≤ b ^ 2) :
    (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) ≤ (a + b) ^ 2 := by
  have hcs := weighted_cauchy_schwarz_sq s w (fun x => (A x) ^ 2)
    (fun x => (B x) ^ 2) hw
  have hA0 : 0 ≤ ∑ x ∈ s, w x * (A x) ^ 4 :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (by positivity))
  have hB0 : 0 ≤ ∑ x ∈ s, w x * (B x) ^ 4 :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (by positivity))
  have hprod := mul_le_mul hA hB hB0 (sq_nonneg a)
  have hpow : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := fun x => by ring
  simp_rw [hpow] at hcs
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcross : (∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) ≤ a * b := by
    nlinarith [sq_nonneg ((∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) - a * b)]
  have hexpand : (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) =
      (∑ x ∈ s, w x * (A x) ^ 4) +
      2 * (∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) +
      (∑ x ∈ s, w x * (B x) ^ 4) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hexpand]
  nlinarith

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.weighted_fourth_moment_add_sq.{u} := @_root_.OAI.Problem313.weighted_fourth_moment_add_sq.{u}
