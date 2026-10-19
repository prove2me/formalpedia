-- Prove2me | solution 1 for OAI.GaussianPropeller.Translation.stdGaussian_map_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:52:57.972978+00:00
-- url     : https://prove2.me/submissions/bb200a09-f9de-41a9-a9e5-fe2b0e993121

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Translation.lean:L119-L136
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Translation.stdGaussian_map_add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation

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

lemma map_density_comp {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hg]
  change (∫⁻ a, (h ∘ g) a ∂μ.withDensity (f ∘ g)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hg) (hh.comp hg),
    lintegral_withDensity_eq_lintegral_mul _ hf hh]
  exact (lintegral_map (hf.mul hh) hg).symm

lemma product_density {ι : Type uι} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  have hii (i : ι) : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hn i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) volume :=
    Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hp.restrict (ae_of_all _ (fun x =>
      Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have heq : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      (fun x => ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · simp only [Set.mem_univ_pi] at hx
      rw [Set.indicator_of_mem (show x ∈ univ.pi s by simpa only [Set.mem_univ_pi] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [← integral_indicator (MeasurableSet.univ_pi hs), heq,
    integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun x _ => hn i x) x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))]

lemma pi_gaussian_density {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      volume.withDensity (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (a i) 1 (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
    gaussianPDF_def]
  exact product_density _ (fun i => integrable_gaussianPDFReal (a i) 1)
    (fun i => gaussianPDFReal_nonneg (a i) 1)

lemma measurable_stdDensity {ι : Type uι} [Fintype ι] :
    Measurable (stdDensity : EuclideanSpace ℝ ι → ℝ) := by
  unfold stdDensity
  fun_prop

lemma stdGaussian_density {ι : Type uι} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal (stdDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density (fun _ => 0)]
  have hm := map_density_comp (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (PiLp.volume_preserving_toLp ι).measurable
    (fun x => ENNReal.ofReal (stdDensity x))
    (measurable_stdDensity.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hm
  exact hm

lemma stdDensity_pos {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    0 < stdDensity x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by norm_num)

lemma stdDensity_eq {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    stdDensity x = (Real.sqrt (2*Real.pi))⁻¹ ^ (Fintype.card ι) *
      Real.exp (-‖x‖^2/2) := by
  simp only [stdDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simp [EuclideanSpace.norm_sq_eq]

lemma stdDensity_add {ι : Type uι} [Fintype ι]
    (x v : EuclideanSpace ℝ ι) :
    stdDensity (x+v) = stdDensity x * Real.exp (-⟪v,x⟫-‖v‖^2/2) := by
  rw [stdDensity_eq, stdDensity_eq, mul_assoc, ← Real.exp_add]
  congr 2
  rw [norm_add_sq_real, real_inner_comm x v]
  ring

lemma stdGaussian_map_add {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x+v) =
      (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (⟪v,x⟫-‖v‖^2/2))) := by
  have hm := map_density_comp (volume : Measure (EuclideanSpace ℝ ι))
    (fun x => x+v) (by fun_prop)
    (fun x => ENNReal.ofReal (stdDensity (x-v))) (by
      exact measurable_stdDensity.comp (by fun_prop) |>.ennreal_ofReal)
  simp only [Function.comp_def, add_sub_cancel_right] at hm
  rw [(measurePreserving_add_right volume v).map_eq] at hm
  rw [stdGaussian_density, hm, ← withDensity_mul volume
    measurable_stdDensity.ennreal_ofReal (by fun_prop)]
  congr 1
  funext x
  rw [sub_eq_add_neg, stdDensity_add, inner_neg_left, norm_neg, neg_neg,
    ENNReal.ofReal_mul (le_of_lt (stdDensity_pos x))]
  rfl

end GaussianPropeller.Translation

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Translation
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.Translation.stdGaussian_map_add.{uι} := @_root_.OAI.GaussianPropeller.Translation.stdGaussian_map_add.{uι}
