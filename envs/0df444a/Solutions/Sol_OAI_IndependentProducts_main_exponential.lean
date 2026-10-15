-- Prove2me | solution 1 for OAI.IndependentProducts.main_exponential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:50:36.77407+00:00
-- url     : https://prove2.me/submissions/3dfb33df-4ff9-44c2-b4a3-e79b17548a48

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/Main.lean:L54-L64
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.IndependentProducts.main_exponential.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_IndependentProducts_main_exponential) verbatim and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialMixture
import Theorems.Thm_OAI_IndependentProducts_averaged_midpoint_from_scalar
import Theorems.Thm_OAI_IndependentProducts_excessConstant_pos
import Theorems.Thm_OAI_IndependentProducts_exponential_scalar_excess

-- ---- from OAI.Analysis.ProductSpaces.ExponentialLaw ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uE

namespace IndependentProducts

lemma exponentialLaw_density : exponentialLaw =
    (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) := by
  change volume.withDensity (exponentialPDF 1) = _
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rw [exponentialPDF_eq]
  by_cases hp : 0 < x
  · simp [hp.le, hp]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [not_le.mpr hn, hp]

lemma exponentialLaw_positive : ∀ᵐ x ∂exponentialLaw, 0 < x := by
  rw [exponentialLaw_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (self_mem_ae_restrict measurableSet_Ioi)

lemma integral_exponentialLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (∫ x, f x ∂exponentialLaw) = ∫ x in Ioi 0, Real.exp (-x) • f x := by
  rw [exponentialLaw_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma integrable_exponentialLaw_iff {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : Integrable f exponentialLaw ↔
      Integrable (fun x => Real.exp (-x) • f x) (volume.restrict (Ioi 0)) := by
  rw [exponentialLaw_density, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma exponentialLaw_integrable_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) exponentialLaw := by
  rw [integrable_exponentialLaw_iff]
  simpa only [IntegrableOn, add_sub_cancel_right, Real.rpow_natCast, smul_eq_mul]
    using Real.GammaIntegral_convergent (s := n + 1) (by positivity)

lemma exponentialLaw_pow_integral (n : ℕ) : (∫ x : ℝ, x ^ n ∂exponentialLaw) = n.factorial := by
  rw [integral_exponentialLaw]
  have h := Real.Gamma_eq_integral (s := n + 1) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  exact h.symm

lemma exponentialLaw_mean : (∫ x : ℝ, x ∂exponentialLaw) = 1 := by
  simpa using exponentialLaw_pow_integral 1

lemma exponentialLaw_second : (∫ x : ℝ, x ^ 2 ∂exponentialLaw) = 2 := by
  simpa using exponentialLaw_pow_integral 2

lemma exponentialLaw_memLp : MemLp (fun x : ℝ => x) 2 exponentialLaw :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (exponentialLaw_integrable_pow 2)

end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.Main ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts

lemma exponentialLaw_hypotheses : MultiplierHypotheses exponentialLaw := by
  refine ⟨inferInstance, exponentialLaw_positive, ?_, exponentialLaw_mean, exponentialLaw_memLp⟩
  intro c hc
  have h1 : (1 : ℝ) = c := by
    calc
      1 = ∫ w : ℝ, w ∂exponentialLaw := exponentialLaw_mean.symm
      _ = ∫ _ : ℝ, c ∂exponentialLaw := integral_congr_ae hc
      _ = c := by simp
  have h2 : (∫ w : ℝ, w ^ 2 ∂exponentialLaw) = c ^ 2 := by
    calc
      _ = ∫ _ : ℝ, c ^ 2 ∂exponentialLaw :=
        integral_congr_ae (hc.mono fun w hw => congrArg (fun x : ℝ => x ^ 2) hw)
      _ = _ := by simp
  rw [exponentialLaw_second, ← h1] at h2
  norm_num at h2

lemma exponential_midpoint_parameter (t K : ℝ) (ht : 0 < t) (hK : 0 < K) :
    excessConstant K * (t / 3 - 1 / K) ≤
      averagedMidpointModulus (productSpan exponentialLaw)
        (normSeminorm ℝ (productSpan exponentialLaw)) t := by
  have hc : 0 ≤ excessConstant K := (excessConstant_pos K).le
  have hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂exponentialLaw) := by
    rw [exponentialLaw_second]
    positivity
  have h := averaged_midpoint_from_scalar exponentialLaw exponentialLaw_hypotheses
    t (t * excessConstant K) (excessConstant K / K) ht.le (mul_nonneg ht.le hc)
    (div_nonneg hc hK.le) hC
    (fun ι _ a b r hr => exponential_scalar_excess a b K t r hK ht.le hr)
  rw [exponentialLaw_second] at h
  apply le_trans _ h
  have hs : 2 * Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hd : t / 3 ≤ t / (2 * Real.sqrt 2) :=
    div_le_div_of_nonneg_left ht.le (by positivity) hs
  have hh := mul_le_mul_of_nonneg_left hd hc
  calc
    excessConstant K * (t / 3 - 1 / K) =
        excessConstant K * (t / 3) - excessConstant K / K := by ring
    _ ≤ excessConstant K * (t / (2 * Real.sqrt 2)) - excessConstant K / K :=
      sub_le_sub_right hh _
    _ = t * excessConstant K / (2 * Real.sqrt 2) - excessConstant K / K := by ring

theorem main_exponential (t : ℝ) (ht : 0 < t) :
    (7 * t / 30) * excessConstant (10 / t) ≤
      averagedMidpointModulus (productSpan exponentialLaw)
        (normSeminorm ℝ (productSpan exponentialLaw)) t ∧
    0 < (7 * t / 30) * excessConstant (10 / t) := by
  constructor
  · have h := exponential_midpoint_parameter t (10 / t) ht (by positivity)
    convert h using 1
    field_simp
    ring
  · exact mul_pos (by positivity) (excessConstant_pos _)

end IndependentProducts

end

end OAI

-- ---- mission target ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (t : ℝ) (ht : 0 < t) :
    (7 * t / 30) * excessConstant (10 / t) ≤
      averagedMidpointModulus (productSpan exponentialLaw)
        (normSeminorm ℝ (productSpan exponentialLaw)) t ∧
    0 < (7 * t / 30) * excessConstant (10 / t) := by
  first
    | exact OAI.IndependentProducts.main_exponential t ht
    | exact OAI.IndependentProducts.main_exponential X t ht
    | exact OAI.IndependentProducts.main_exponential
    | (apply OAI.IndependentProducts.main_exponential <;> assumption)
    | (intros; apply OAI.IndependentProducts.main_exponential <;> assumption)
