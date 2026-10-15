-- Prove2me | solution 1 for OAI.SquareRootDegree.SmoothGaussian.beta_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:20:52.975626+00:00
-- url     : https://prove2.me/submissions/8a07c42f-d35c-4d4b-b3c9-4d12397bcf71

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SmoothGaussian.lean:L80-L113
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.SmoothGaussian.beta_lower. The node keeps its source
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

theorem tent_nonneg (a h x : ℝ) : 0 ≤ tent a h x := le_max_left _ _

theorem tent_eq_zero {a h x : ℝ} (hh : 0 < h) (hx : h ≤ |x-a|) :
    tent a h x = 0 := by
  unfold tent
  apply max_eq_left
  have : 1 ≤ |x-a|/h := (one_le_div hh).mpr hx
  linarith

theorem tent_ne_zero_iff {a h x : ℝ} (hh : 0 < h) :
    tent a h x ≠ 0 ↔ |x-a| < h := by
  constructor
  · intro hn
    exact lt_of_not_ge (fun hx => hn (tent_eq_zero hh hx))
  · intro hx
    apply ne_of_gt
    apply lt_of_lt_of_le _ (le_max_right _ _)
    have := (div_lt_one hh).mpr hx
    linarith

theorem tent_support {a h : ℝ} (hh : 0 < h) :
    Function.support (tent a h) ⊆ Set.Icc (a-h) (a+h) := by
  intro x hx
  have he := (tent_ne_zero_iff hh).mp hx
  rw [abs_lt] at he
  constructor <;> linarith

theorem tent_compactSupport {a h : ℝ} (hh : 0 < h) : HasCompactSupport (tent a h) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a-h) (b := a+h))
  intro x hx
  by_contra hn
  exact hx (tent_support hh hn)

theorem tent_half {a h x : ℝ} (hh : 0 < h) (hx : |x-a| ≤ h/2) :
    1/2 ≤ tent a h x := by
  apply le_trans _ (le_max_right _ _)
  have : |x-a|/h ≤ 1/2 := (div_le_iff₀ hh).mpr (by linarith)
  linarith

theorem integrable_tent_mul {a h : ℝ} (hh : 0 < h) (p : ℝ → ℝ) (hp : Continuous p)
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun x => tent a h x * p x) μ := by
  apply ((continuous_tent a h).mul hp).integrable_of_hasCompactSupport
  exact (tent_compactSupport hh).mul_right

theorem pdf_lower {A x : ℝ} (hx : |x| ≤ A) :
    (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(A^2)/2) ≤ gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have : x^2 ≤ A^2 := by nlinarith [abs_nonneg x, sq_abs x]
  linarith

theorem beta_lower {a h : ℝ} (hh : 0 < h) :
    h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2)) ≤
      ∫ x, tent a h x ∂gaussianReal 0 1 := by
  let c := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha := integrable_tent_mul (a := a) hh (gaussianPDFReal 0 1) (by
    unfold gaussianPDFReal; fun_prop) volume
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  change h/2*c ≤ ∫ x, gaussianPDFReal 0 1 x * tent a h x
  have hi : Integrable (fun x => gaussianPDFReal 0 1 x * tent a h x) volume := by
    simpa only [mul_comm] using ha
  have hset : ∫ x in Set.Icc (a-h/2) (a+h/2), c/2 ≤
      ∫ x in Set.Icc (a-h/2) (a+h/2), gaussianPDFReal 0 1 x * tent a h x := by
    apply integral_mono_ae (integrable_const _) hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hab : |x-a| ≤ h/2 := abs_le.mpr (by constructor <;> linarith [hx.1,hx.2])
    have hp : c ≤ gaussianPDFReal 0 1 x := by
      apply pdf_lower
      calc |x| = |(x-a)+a| := by congr 1; ring
        _ ≤ |x-a|+|a| := abs_add_le _ _
        _ ≤ |a|+h := by linarith
    have hw := tent_half hh hab
    calc c/2 = c * (1/2) := by ring
      _ ≤ gaussianPDFReal 0 1 x * tent a h x :=
        mul_le_mul hp hw (by norm_num) (gaussianPDFReal_nonneg ..)
  have hs : ∫ x in Set.Icc (a-h/2) (a+h/2), gaussianPDFReal 0 1 x * tent a h x ≤
      ∫ x, gaussianPDFReal 0 1 x * tent a h x := by
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun x => mul_nonneg (gaussianPDFReal_nonneg ..) (tent_nonneg ..))) hi
  apply le_trans _ (hset.trans hs)
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ a+h/2-(a-h/2))]
  ring_nf
  exact le_rfl

end SmoothGaussian
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SmoothGaussian
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

theorem solution {a h : ℝ} (hh : 0 < h) :
    h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2)) ≤
      ∫ x, tent a h x ∂gaussianReal 0 1 := by
  first
    | exact OAI.SquareRootDegree.SmoothGaussian.beta_lower hh
    | exact OAI.SquareRootDegree.SmoothGaussian.beta_lower
    | (apply OAI.SquareRootDegree.SmoothGaussian.beta_lower <;> assumption)
    | (intros; apply OAI.SquareRootDegree.SmoothGaussian.beta_lower <;> assumption)
