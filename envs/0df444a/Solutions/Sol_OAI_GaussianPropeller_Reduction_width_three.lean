-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.width_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:41:52.26799+00:00
-- url     : https://prove2.me/submissions/5f530ff5-cf94-4867-a00c-f3238af13841

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Attainment.lean:L91-L116
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.width_three. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment

-- ---- from OAI.Probability.GaussianPropeller.Moments ----
namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem scoreMax_le_iff (v : Fin k → Space d) (x : Space d) (b : ℝ) :
    scoreMax v x ≤ b ↔ ∀ i, ⟪v i, x⟫ ≤ b := by
  simp only [scoreMax, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem continuous_scoreMax (v : Fin k → Space d) : Continuous (scoreMax v) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)

theorem norm_scoreMax_le (v : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x‖ ≤ ‖v‖ * ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_scoreMax v.ofLp x
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg x))

theorem integrable_scoreMax (v : Tuple d k) :
    Integrable (scoreMax v.ofLp) (gaussian d) := by
  apply ((integrable_id_gaussian d).norm.const_mul ‖v‖).mono'
    (continuous_scoreMax v.ofLp).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_scoreMax_le v)

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Analytic ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic

theorem integral_pos_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ in Ioi 0, r * Real.exp (-b * r ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hd (x : ℝ) : HasDerivAt (fun x => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    apply (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)).congr_deriv
    field_simp [hb']
    ring
  have ht : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht using 1
  simp

theorem integral_abs_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ, |r| * Real.exp (-b * r ^ 2) = b⁻¹ := by
  let f : ℝ → ℝ := fun r => |r| * Real.exp (-b * r ^ 2)
  have hf : Integrable f := by
    simpa only [f, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hb).abs
  have hpos : ∫ r in Ioi 0, f r = (2 * b)⁻¹ := by
    rw [← integral_pos_mul_exp hb]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
      simp only [f, abs_of_pos (show (0 : ℝ) < r from hr)])
  have hneg : ∫ r in Iic 0, f r = ∫ r in Ioi 0, f r := by
    calc
      ∫ r in Iic 0, f r = ∫ r in Ioi 0, f (-r) := by
        simpa [f] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ r in Ioi 0, f r := by simp only [f, abs_neg, neg_sq]
  change (∫ r, f r) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, hneg, hpos]
  field_simp
  ring

theorem integral_abs_gaussianReal_std :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = 2 / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
    rw [show -(x ^ 2) / (2 : ℝ) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [hfun, integral_const_mul, integral_abs_mul_exp (by norm_num : (0 : ℝ) < 1/2)]
  norm_num
  ring

theorem integral_abs_dual_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    ∫ x, |L x| ∂stdGaussian E = ‖L‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  have hm : (stdGaussian E).map L = (gaussianReal 0 1).map (‖L‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one, Real.toNNReal_of_nonneg (sq_nonneg ‖L‖)]
  rw [← integral_map L.continuous.aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => |x|) ((stdGaussian E).map L)), hm,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (norm_nonneg L)]
  rw [integral_const_mul, integral_abs_gaussianReal_std]

theorem integral_abs_inner_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    ∫ x, |⟪v, x⟫| ∂stdGaussian E = ‖v‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  simpa only [InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.norm_map] using
    integral_abs_dual_stdGaussian (InnerProductSpace.toDual ℝ E v)

end GaussianPropeller.Analytic

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Attainment ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem integral_comp_neg {d : ℕ} (f : Space d → ℝ) (hf : AEStronglyMeasurable f (gaussian d)) :
    ∫ x, f (-x) ∂gaussian d = ∫ x, f x ∂gaussian d := by
  have hm : (gaussian d).map (fun x => -x) = gaussian d :=
    stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  rw [← integral_map (by fun_prop) (hm.symm ▸ hf), hm]

theorem scoreMax_three {d : ℕ} (v : Fin 3 → Space d) (x : Space d) :
    scoreMax v x = max ⟪v 0, x⟫ (max ⟪v 1, x⟫ ⟪v 2, x⟫) := by
  apply le_antisymm
  · apply (scoreMax_le_iff v x _).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact max_le (le_scoreMax v 0 x) (max_le (le_scoreMax v 1 x) (le_scoreMax v 2 x))

theorem three_range_identity (a b c : ℝ) :
    max a (max b c) + max (-a) (max (-b) (-c)) =
      (|a - b| + |a - c| + |b - c|) / 2 := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · simp [max_eq_right hbc, max_eq_right (hab.trans hbc),
        max_eq_left (neg_le_neg hbc), max_eq_left (neg_le_neg hab),
        abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hbc),
        abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc))]
      ring
    · rcases le_total a c with hac | hca
      · simp [max_eq_left hcb, max_eq_right hab,
          max_eq_right (neg_le_neg hcb), max_eq_left (neg_le_neg hac),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hac),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
      · simp [max_eq_left hcb, max_eq_right hab,
          max_eq_right (neg_le_neg hcb), max_eq_right (neg_le_neg hca),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
  · rcases le_total a c with hac | hca
    · simp [max_eq_right (hba.trans hac), max_eq_right hac,
        max_eq_left (neg_le_neg (hba.trans hac)), max_eq_right (neg_le_neg hba),
        abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonpos (sub_nonpos.mpr hac),
        abs_of_nonpos (sub_nonpos.mpr (hba.trans hac))]
      ring
    · rcases le_total b c with hbc | hcb
      · simp [max_eq_right hbc, max_eq_left hca,
          max_eq_left (neg_le_neg hbc), max_eq_right (neg_le_neg hba),
          abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonpos (sub_nonpos.mpr hbc)]
        ring
      · simp [max_eq_left hcb, max_eq_left hba,
          max_eq_right (neg_le_neg hcb), max_eq_right (neg_le_neg hca),
          abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring

theorem width_three {d : ℕ} (v : Tuple d 3) :
    width v = (‖v.ofLp 0 - v.ofLp 1‖ + ‖v.ofLp 0 - v.ofLp 2‖ +
      ‖v.ofLp 1 - v.ofLp 2‖) / (2 * Real.sqrt (2 * Real.pi)) := by
  have he (x : Space d) : scoreMax v.ofLp x + scoreMax v.ofLp (-x) =
      (|⟪v.ofLp 0 - v.ofLp 1, x⟫| + |⟪v.ofLp 0 - v.ofLp 2, x⟫| +
        |⟪v.ofLp 1 - v.ofLp 2, x⟫|) / 2 := by
    simp only [scoreMax_three, inner_neg_right, inner_sub_left]
    exact three_range_identity _ _ _
  have hi (w : Space d) : Integrable (fun x => |⟪w, x⟫|) (gaussian d) :=
    ((integrable_id_gaussian d).const_inner w).abs
  have hneg : Integrable (fun x => scoreMax v.ofLp (-x)) (gaussian d) := by
    convert integrable_scoreMax (-v) using 1
    ext x
    simp only [scoreMax_three, PiLp.neg_apply, inner_neg_left, inner_neg_right]
  have h := integral_congr_ae (μ := gaussian d) (Filter.Eventually.of_forall he)
  rw [integral_add (integrable_scoreMax v) hneg,
    integral_comp_neg _ (integrable_scoreMax v).aestronglyMeasurable,
    integral_div] at h
  rw [integral_add (f := fun x => |⟪v.ofLp 0 - v.ofLp 1, x⟫| +
      |⟪v.ofLp 0 - v.ofLp 2, x⟫|) (g := fun x => |⟪v.ofLp 1 - v.ofLp 2, x⟫|)
      ((hi _).add (hi _)) (hi _), integral_add (hi _) (hi _)] at h
  simp_rw [gaussian, Analytic.integral_abs_inner_stdGaussian] at h
  change width v + width v = _ at h
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp [hs] at h ⊢
  nlinarith only [h]

end GaussianPropeller.Reduction

namespace GaussianPropeller

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.width_three := @_root_.OAI.GaussianPropeller.Reduction.width_three
