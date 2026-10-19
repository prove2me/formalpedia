-- Prove2me | solution 2 for OAI.C0Absorption.exists_uniform_lp_detector
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:37:51.338358+00:00
-- url     : https://prove2.me/submissions/4a644514-218f-49ed-8d36-74fb29710ce6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Lists.lean:L152-L179
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.exists_uniform_lp_detector. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

-- ---- from OAI.Analysis.C0Absorption.Lists ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end CompletedLists

section InterpolationAndDenseLimits

 theorem finite_lp_norm_rpow {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (x : PiLp p (fun _ : ι => ℝ)) :
    ‖x‖ ^ p.toReal = ∑ i, |x i| ^ p.toReal := by
  rw [PiLp.norm_eq_sum hp, ← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

 theorem finite_lp_interpolation {ι : Type*} [Fintype ι]
    (p q : ℝ≥0∞) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (hqp : q.toReal < p.toReal) (x : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, |x i| ≤ δ) :
    ‖WithLp.toLp p x‖ ^ p.toReal ≤
      δ ^ (p.toReal - q.toReal) * ‖WithLp.toLp q x‖ ^ q.toReal := by
  rw [finite_lp_norm_rpow p hp, finite_lp_norm_rpow q hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change |x i| ^ p.toReal ≤ δ ^ (p.toReal - q.toReal) * |x i| ^ q.toReal
  calc
    |x i| ^ p.toReal = |x i| ^ (p.toReal - q.toReal) * |x i| ^ q.toReal := by
      rw [← Real.rpow_add' (abs_nonneg _) (by simpa using hp.ne'), sub_add_cancel]
    _ ≤ δ ^ (p.toReal - q.toReal) * |x i| ^ q.toReal := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (abs_nonneg _) (hδ i) (sub_nonneg.mpr hqp.le))
        (Real.rpow_nonneg (abs_nonneg _) _)

theorem exists_uniform_lp_detector (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hqp : q.toReal < p.toReal)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin n → ℝ),
      a ≤ ‖WithLp.toLp p x‖ → ‖WithLp.toLp q x‖ ≤ B →
      ∃ i, δ < |x i| := by
  let A := a ^ p.toReal
  let D := B ^ q.toReal
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hD : 0 < D := Real.rpow_pos_of_pos hB _
  have hs : 0 < p.toReal - q.toReal := sub_pos.mpr hqp
  let δ := (A / (2 * D)) ^ (1 / (p.toReal - q.toReal))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hA (mul_pos (by norm_num) hD)) _
  have hpow : δ ^ (p.toReal - q.toReal) = A / (2 * D) := by
    rw [show δ = (A / (2 * D)) ^ (1 / (p.toReal - q.toReal)) from rfl,
      ← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  refine ⟨δ, hδ, ?_⟩
  intro n x hlow hupp
  by_contra! hnone
  have hint := finite_lp_interpolation p q hp hq hqp x δ hnone
  have hlu : A ≤ ‖WithLp.toLp p x‖ ^ p.toReal := Real.rpow_le_rpow ha.le hlow hp.le
  have huu : ‖WithLp.toLp q x‖ ^ q.toReal ≤ D :=
    Real.rpow_le_rpow (norm_nonneg _) hupp hq.le
  have hb := mul_le_mul_of_nonneg_left huu (Real.rpow_nonneg hδ.le (p.toReal - q.toReal))
  rw [hpow] at hint hb
  have heq : A / (2 * D) * D = A / 2 := by field_simp [ne_of_gt hD]
  rw [heq] at hb
  linarith

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution : type_of% @_root_.OAI.C0Absorption.exists_uniform_lp_detector := @_root_.OAI.C0Absorption.exists_uniform_lp_detector
