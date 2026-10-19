-- Prove2me | solution 1 for OAI.GaussianPropeller.EhrhardCone.prob_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:19:42.447982+00:00
-- url     : https://prove2.me/submissions/a2acce02-b044-4950-bd43-d49258d4dcdd

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean:L50-L76
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.EhrhardCone.prob_mem. The node keeps its source
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

end GaussianPropeller.Translation

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ConeConcavity ----
namespace OAI

universe uX uι uκ

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

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

omit [Nonempty κ] in
lemma measurableSet_shifted [Nonempty κ] (v : κ → E) (x : E) : MeasurableSet (shifted v x) := by
  change MeasurableSet {y : E | ∀ i, 0 ≤ ⟪v i,x+y⟫}
  simpa only [ofPred_forall] using MeasurableSet.iInter (fun i =>
    measurableSet_le (measurable_const : Measurable (fun _ : E => (0:ℝ)))
      (show Measurable (fun y : E => ⟪v i,x+y⟫) by fun_prop))

lemma gaussian_open_pos {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) : 0 < γ U := by
  have hac : (volume : Measure E) ≪ γ := by
    rw [Translation.stdGaussian_density]
    exact withDensity_absolutelyContinuous' Translation.measurable_stdDensity.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (Translation.stdDensity_pos x))))
  by_contra! hz
  have heq : γ U = 0 := le_antisymm hz bot_le
  exact ne_of_gt (hU.measure_pos volume hne) (hac heq)

lemma prob_mem (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (x : E) :
    prob v x ∈ Ioo (0:ℝ) 1 := by
  let U : Set E := {y | ∀ i, 0 < ⟪v i,x+y⟫}
  have hU : IsOpen U := by
    simpa only [U, ofPred_forall] using isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_const : Continuous (fun _ : E => (0:ℝ)))
        (show Continuous (fun y : E => ⟪v i,x+y⟫) by fun_prop))
  have hn : U.Nonempty := ⟨e-x, by simpa only [U, mem_ofPred_eq, show x+(e-x)=e by abel] using he⟩
  have hs : U ⊆ shifted v x := fun y hy i => (hy i).le
  have hp : 0 < (γ).real (shifted v x) := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hU hn).trans_le (measure_mono hs))) (measure_ne_top _ _)
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hv : v i ≠ 0 := by intro hh; simpa only [hh, inner_zero_left, lt_self_iff_false] using he i
  let V : Set E := {y | ⟪v i,x+y⟫ < 0}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hnV : V.Nonempty := by
    refine ⟨-v i-x,?_⟩
    change ⟪v i,x+(-v i-x)⟫ < 0
    rw [show x+(-v i-x)= -v i by abel, inner_neg_right]
    exact neg_neg_of_pos (real_inner_self_pos.mpr hv)
  have hsV : V ⊆ (shifted v x)ᶜ := by
    intro y hy hz
    exact (not_lt_of_ge (hz i)) hy
  have hc : 0 < (γ).real (shifted v x)ᶜ := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hV hnV).trans_le (measure_mono hsV))) (measure_ne_top _ _)
  rw [probReal_compl_eq_one_sub (measurableSet_shifted v x)] at hc
  exact ⟨hp, by change (γ).real (shifted v x) < 1; linarith only [hc]⟩

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

end GaussianPropeller.EhrhardCone

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.EhrhardCone
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
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth


theorem solution.{uι,uκ} : type_of% @_root_.OAI.GaussianPropeller.EhrhardCone.prob_mem.{uι,uκ} := @_root_.OAI.GaussianPropeller.EhrhardCone.prob_mem.{uι,uκ}
