-- Prove2me | solution 1 for OAI.GaussianPropeller.Stein.integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:56:04.992988+00:00
-- url     : https://prove2.me/submissions/c740b277-7774-44ba-8fa9-bdf28ea4c065

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Stein.lean:L67-L102
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Stein.integration_by_parts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Theorems.Thm_OAI_GaussianPropeller_Translation_stdGaussian_map_add

-- ---- from OAI.Probability.GaussianPropeller.Translation ----
namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

lemma integrable_exp_inner {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (t : ℝ) : Integrable (fun x => Real.exp (t*⟪h,x⟫)) (stdGaussian E) := by
  let L : StrongDual ℝ E := innerSL ℝ h
  have hi : Integrable (fun x : ℝ => Real.exp (t*x)) ((stdGaussian E).map L) := by
    rw [IsGaussian.map_eq_gaussianReal L]
    exact integrable_exp_mul_gaussianReal t
  exact hi.comp_aemeasurable L.continuous.aemeasurable

end GaussianPropeller.Translation

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Stein ----
namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

open Filter
open scoped Topology
namespace GaussianPropeller.Stein
open GaussianPropeller.Translation

variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma integrable_bounded {H : E → ℝ} (hH : AEStronglyMeasurable H γ)
    {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) : Integrable H γ :=
  Integrable.mono' (integrable_const B) hH (ae_of_all _ hB)

lemma translation_expectation (v : E) {H : E → ℝ} (hH : Continuous H) :
    ∫ x, H (x+v) ∂γ = ∫ x, Real.exp (⟪v,x⟫-‖v‖^2/2)*H x ∂γ := by
  rw [← integral_map (by fun_prop) hH.aestronglyMeasurable, stdGaussian_map_add]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)), smul_eq_mul]

lemma weighted_mgf_derivative {H : E → ℝ} (hH : Continuous H)
    {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) (v : E) :
    HasDerivAt (fun s : ℝ => ∫ x, H x*Real.exp (s*⟪v,x⟫) ∂γ)
      (∫ x, H x*⟪v,x⟫ ∂γ) 0 := by
  have hB0 : 0 ≤ B := (norm_nonneg (H 0)).trans (hB 0)
  have hi : Integrable (fun x : E => |⟪v,x⟫| *Real.exp |⟪v,x⟫|) γ := by
    simpa using (integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := fun x : E => ⟪v,x⟫) (v := 0) (t := 2) (x := 1)
      (by simpa using integrable_exp_inner v 2)
      (by simpa using integrable_exp_inner v (-2)) (by norm_num) (by norm_num) 1)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (x₀ := 0) (F := fun s : ℝ => fun x : E => H x*Real.exp (s*⟪v,x⟫))
    (F' := fun s x => H x*(Real.exp (s*⟪v,x⟫)*⟪v,x⟫))
    (s := Ioo (-1) 1) (bound := fun x => B*(|⟪v,x⟫| *Real.exp |⟪v,x⟫|))
    (by exact Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall (fun s => by fun_prop))
    (by simpa using integrable_bounded hH.aestronglyMeasurable hB)
    (by fun_prop) ?_ (hi.const_mul B) ?_
  · simpa [mul_comm, mul_left_comm, mul_assoc] using hd.2
  · filter_upwards [] with x s hs
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hs1 : |s| ≤ 1 := (abs_lt.mpr hs).le
    have he : Real.exp (s*⟪v,x⟫) ≤ Real.exp |⟪v,x⟫| := by
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by rw [abs_mul]; nlinarith [abs_nonneg ⟪v,x⟫])
    calc
      |H x| *(Real.exp (s*⟪v,x⟫)*|⟪v,x⟫|) ≤ B*(Real.exp |⟪v,x⟫| *|⟪v,x⟫|) :=
        mul_le_mul (hB x) (mul_le_mul_of_nonneg_right he (abs_nonneg _))
          (by positivity) hB0
      _ = _ := by ring
  · filter_upwards [] with x s _
    simpa only [id_eq, one_mul] using (((hasDerivAt_id s).mul_const ⟪v,x⟫).exp).const_mul (H x)

lemma integration_by_parts {H : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt H (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C) (v : E) :
    ∫ x, D x v ∂γ = ∫ x, H x*⟪v,x⟫ ∂γ := by
  have hc : Continuous H := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (x₀ := 0) (F := fun s : ℝ => fun x : E => H (x+s•v))
    (F' := fun s x => D (x+s•v) v) (s := univ)
    (bound := fun _ => C*‖v‖) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun s => by fun_prop))
    (by simpa using integrable_bounded hc.aestronglyMeasurable hB)
    (by fun_prop) (ae_of_all _ (fun x s _ =>
      (D (x+s•v)).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))))
    (integrable_const _) (ae_of_all _ (fun x s _ => by
      simpa only [Function.comp_def, one_smul, id_eq] using (hD (x+s•v)).comp_hasDerivAt s
        ((hasDerivAt_id s).smul_const v |>.const_add x)))
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s^2*‖v‖^2/2)) 0 0 := by
    convert (((hasDerivAt_pow 2 (0:ℝ)).neg.mul_const (‖v‖^2)).div_const 2).exp using 1 <;> simp
  have hr := he.mul (weighted_mgf_derivative hc hB v)
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_mul, zero_div,
    Real.exp_zero, one_mul, zero_add] at hr
  have heq : (fun s : ℝ => Real.exp (-s^2*‖v‖^2/2)*
      (∫ x, H x*Real.exp (s*⟪v,x⟫) ∂γ)) = (fun s : ℝ => ∫ x, H (x+s•v) ∂γ) := by
    funext s
    rw [translation_expectation _ hc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      starRingEnd_apply, star_trivial]
    rw [mul_left_comm, ← Real.exp_add]
    rw [show -s^2*‖v‖^2/2+s*⟪v,x⟫ = s*⟪v,x⟫-s^2*‖v‖^2/2 by ring]
    ring
  change HasDerivAt (fun s : ℝ => Real.exp (-s^2*‖v‖^2/2)*
      (∫ x, H x*Real.exp (s*⟪v,x⟫) ∂γ)) _ 0 at hr
  rw [heq] at hr
  simpa using hd.2.unique hr

end GaussianPropeller.Stein

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Stein
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open GaussianPropeller.Translation


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.Stein.integration_by_parts.{uι} := @_root_.OAI.GaussianPropeller.Stein.integration_by_parts.{uι}
