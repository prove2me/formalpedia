-- Prove2me | solution 1 for OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:23:23.732401+00:00
-- url     : https://prove2.me/submissions/8eed400c-8c50-4d15-8384-5ddf956d5920

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SmoothGaussian.lean:L151-L203
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothGaussian ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

theorem integral_weight_sub_sq (μ : Measure ℝ) (w : ℝ → ℝ)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x * x) μ)
    (h2 : Integrable (fun x => w x * x^2) μ) (c : ℝ) :
    (∫ x, w x * (x-c)^2 ∂μ) = (∫ x, w x * x^2 ∂μ) -
      2*c*(∫ x, w x * x ∂μ) + c^2*mass μ w := by
  have he : (fun x => w x * (x-c)^2) = fun x =>
      w x * x^2 - (2*c)*(w x*x) + c^2*w x := by funext x; ring
  rw [he, integral_add (f := fun x => w x*x^2-(2*c)*(w x*x))
    (g := fun x => c^2*w x) (h2.sub (h1.const_mul (2*c))) (h0.const_mul (c^2)),
    integral_sub h2 (h1.const_mul (2*c)), integral_const_mul, integral_const_mul]
  rfl

theorem mean_mul_mass (μ : Measure ℝ) (w : ℝ → ℝ) (hb : mass μ w ≠ 0) :
    mean μ w * mass μ w = ∫ x, w x * x ∂μ := by
  simp [mean, hb]

theorem variance_mul_mass (μ : Measure ℝ) (w : ℝ → ℝ)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x * x) μ)
    (h2 : Integrable (fun x => w x * x^2) μ) (hb : mass μ w ≠ 0) :
    variance μ w * mass μ w = ∫ x, w x * (x-mean μ w)^2 ∂μ := by
  rw [integral_weight_sub_sq μ w h0 h1 h2]
  have hm := mean_mul_mass μ w hb
  rw [← hm]
  unfold variance
  field_simp [hb]
  ring

theorem weighted_interval_bounds (μ : Measure ℝ) (w : ℝ → ℝ) {a h : ℝ}
    (hh : 0 ≤ h) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x, w x ≠ 0 → |x-a| ≤ h)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x*x) μ)
    (h2 : Integrable (fun x => w x*x^2) μ) (hb : 0 < mass μ w) :
    |mean μ w-a| ≤ h ∧ 0 ≤ variance μ w ∧ variance μ w ≤ h^2 := by
  have hlo : (a-h)*mass μ w ≤ ∫ x, w x*x ∂μ := by
    rw [mass, ← integral_const_mul]
    apply integral_mono (h0.const_mul _) h1
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have ht := (abs_le.mp (hs x hx)).1
      nlinarith [mul_nonneg (hw x) (show 0 ≤ x-(a-h) by linarith)]
  have hhi : (∫ x, w x*x ∂μ) ≤ (a+h)*mass μ w := by
    rw [mass, ← integral_const_mul]
    apply integral_mono h1 (h0.const_mul _)
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have ht := (abs_le.mp (hs x hx)).2
      nlinarith [mul_nonneg (hw x) (show 0 ≤ (a+h)-x by linarith)]
  have hm := mean_mul_mass μ w hb.ne'
  have hmean : |mean μ w-a| ≤ h := by
    rw [abs_le]
    constructor <;> nlinarith
  have hv := variance_mul_mass μ w h0 h1 h2 hb.ne'
  have hv0 : 0 ≤ variance μ w := by
    have hn : 0 ≤ ∫ x, w x*(x-mean μ w)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg (x-mean μ w)))
    rw [← hv] at hn
    exact nonneg_of_mul_nonneg_left hn hb
  have hsq : ∫ x, w x*(x-a)^2 ∂μ ≤ h^2*mass μ w := by
    rw [mass, ← integral_const_mul]
    have he : Integrable (fun x => w x*(x-a)^2) μ := by
      convert! (h2.sub (h1.const_mul (2*a))).add (h0.const_mul (a^2)) using 1
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    apply integral_mono he (h0.const_mul _)
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have ht : (x-a)^2 ≤ h^2 := by nlinarith [sq_abs (x-a),hs x hx, abs_nonneg (x-a)]
      nlinarith [mul_nonneg (hw x) (sub_nonneg.mpr ht)]
  rw [integral_weight_sub_sq μ w h0 h1 h2] at hsq
  have hmoment : (∫ x, w x*x^2 ∂μ) = (variance μ w + mean μ w^2)*mass μ w := by
    dsimp [variance]
    field_simp [hb.ne']
    ring
  have hvar : variance μ w ≤ h^2 := by
    have he := mul_nonneg hb.le (sq_nonneg (mean μ w-a))
    rw [hmoment, ← hm] at hsq
    nlinarith
  exact ⟨hmean,hv0,hvar⟩

end SmoothGaussian
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SmoothGaussian
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

theorem solution (μ : Measure ℝ) (w : ℝ → ℝ) {a h : ℝ}
    (hh : 0 ≤ h) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x, w x ≠ 0 → |x-a| ≤ h)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x*x) μ)
    (h2 : Integrable (fun x => w x*x^2) μ) (hb : 0 < mass μ w) :
    |mean μ w-a| ≤ h ∧ 0 ≤ variance μ w ∧ variance μ w ≤ h^2 := by
  first
    | exact OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds μ w hh hw hs h0 h1 h2 hb
    | exact OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds
    | (apply OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds <;> assumption)
    | (intros; apply OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds <;> assumption)
