-- Prove2me | solution 3 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T02:24:13.370445+00:00
-- url     : https://prove2.me/submissions/9235c471-469e-4839-af54-2e960db37014
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B076
import Definitions.Def_OAIErdos3B1344
import Definitions.Def_OAIErdos3B1372
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_uniform_budget
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_principalLaw_eq_contained
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_relativePatchSliceConclusion_of_primitive_retained_forecast_score
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_grid_mass_le_v2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

theorem intervalWindow_mem_Icc (a b t : ℝ) : intervalWindow a b t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ioc a b <;> simp [intervalWindow, ht]

theorem intervalWindow_measurable (a b : ℝ) : Measurable (intervalWindow a b) :=
  measurable_const.indicator measurableSet_Ioc

theorem intervalWindow_integrable (a b : ℝ) : Integrable (intervalWindow a b) := by
  exact (integrableOn_const (s := Ioc a b) (μ := volume) (C := (1 : ℝ))
    (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Ioc

theorem integral_intervalWindow (a b : ℝ) :
    (∫ t, intervalWindow a b t) = max (b - a) 0 := by
  rw [intervalWindow, integral_indicator_const (1 : ℝ) measurableSet_Ioc, smul_eq_mul, mul_one,
    Real.volume_real_Ioc]

theorem interval_separation {a b c d t : ℝ} (hs : t ∈ Ioc a b) (ht : t ∉ Ioc c d) :
    t ∈ Ioc (min a c) (max a c) ∨ t ∈ Ioc (min b d) (max b d) := by
  by_cases hct : c < t
  · have hdt : d < t := by
      by_contra h
      exact ht ⟨hct, le_of_not_gt h⟩
    exact Or.inr ⟨(min_le_right b d).trans_lt hdt, hs.2.trans (le_max_left b d)⟩
  · exact Or.inl ⟨(min_le_left a c).trans_lt hs.1, (le_of_not_gt hct).trans (le_max_right a c)⟩

theorem intervalWindow_difference_le (a b c d t : ℝ) :
    |intervalWindow a b t - intervalWindow c d t| ≤
      intervalWindow (min a c) (max a c) t + intervalWindow (min b d) (max b d) t := by
  have h₁ := (intervalWindow_mem_Icc (min a c) (max a c) t).1
  have h₂ := (intervalWindow_mem_Icc (min b d) (max b d) t).1
  by_cases hs : t ∈ Ioc a b <;> by_cases ht : t ∈ Ioc c d
  · simpa [intervalWindow, hs, ht] using add_nonneg h₁ h₂
  · have h := interval_separation hs ht
    simp only [intervalWindow, indicator_of_mem hs, indicator_of_notMem ht, sub_zero, abs_one]
    rcases h with h | h
    · rw [indicator_of_mem h]
      exact le_add_of_nonneg_right h₂
    · rw [indicator_of_mem h]
      exact le_add_of_nonneg_left h₁
  · have h := interval_separation ht hs
    rw [min_comm c a, max_comm c a, min_comm d b, max_comm d b] at h
    simp only [intervalWindow, indicator_of_notMem hs, indicator_of_mem ht, zero_sub, abs_neg, abs_one]
    rcases h with h | h
    · rw [indicator_of_mem h]
      exact le_add_of_nonneg_right h₂
    · rw [indicator_of_mem h]
      exact le_add_of_nonneg_left h₁
  · simpa [intervalWindow, hs, ht] using add_nonneg h₁ h₂

theorem intervalWindow_integral_difference_le (a b c d : ℝ) :
    (∫ t, |intervalWindow a b t - intervalWindow c d t|) ≤ |c - a| + |d - b| := by
  have hf : Integrable (fun t => |intervalWindow a b t - intervalWindow c d t|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((intervalWindow_integrable a b).sub (intervalWindow_integrable c d)).norm
  have hg : Integrable (fun t => intervalWindow (min a c) (max a c) t +
      intervalWindow (min b d) (max b d) t) := by
    exact (intervalWindow_integrable (min a c) (max a c)).add
      (intervalWindow_integrable (min b d) (max b d))
  have h := integral_mono hf hg
    (fun t => intervalWindow_difference_le a b c d t)
  rw [integral_add (intervalWindow_integrable _ _) (intervalWindow_integrable _ _),
    integral_intervalWindow, integral_intervalWindow,
    max_sub_min_eq_abs, max_sub_min_eq_abs,
    max_eq_left (abs_nonneg _), max_eq_left (abs_nonneg _)] at h
  simpa only [abs_sub_comm] using h

theorem intervalWindow_translation_le (a b x y : ℝ) :
    (∫ t, |intervalWindow (x + a) (x + b) t - intervalWindow (y + a) (y + b) t|) ≤ 2 * |x - y| := by
  have h := intervalWindow_integral_difference_le (x + a) (x + b) (y + a) (y + b)
  simpa only [add_sub_add_right_eq_sub, abs_sub_comm, two_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem normalizedIntervalWindow_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (x t : ℝ) :
    0 ≤ normalizedIntervalWindow ℓ x t := div_nonneg (intervalWindow_mem_Icc _ _ _).1 hℓ.le

theorem normalizedIntervalWindow_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x t : ℝ) :
    normalizedIntervalWindow ℓ x t ≤ 1 / ℓ :=
  div_le_div_of_nonneg_right (intervalWindow_mem_Icc _ _ _).2 hℓ.le

theorem normalizedIntervalWindow_integrable (ℓ x : ℝ) :
    Integrable (normalizedIntervalWindow ℓ x) := (intervalWindow_integrable _ _).div_const ℓ

theorem normalizedIntervalWindow_measurable (ℓ x : ℝ) :
    Measurable (normalizedIntervalWindow ℓ x) := (intervalWindow_measurable _ _).div_const ℓ

theorem normalizedIntervalWindow_mass {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    (∫ t, normalizedIntervalWindow ℓ x t) = 1 := by
  unfold normalizedIntervalWindow
  rw [integral_div, integral_intervalWindow]
  simp only [add_sub_cancel_left, max_eq_left hℓ.le, div_self hℓ.ne']

theorem normalizedIntervalWindow_translation_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : ℝ) :
    (∫ t, |normalizedIntervalWindow ℓ x t - normalizedIntervalWindow ℓ y t|) ≤
      2 / ℓ * |x - y| := by
  have heq (t : ℝ) : |normalizedIntervalWindow ℓ x t - normalizedIntervalWindow ℓ y t| =
      |intervalWindow x (x + ℓ) t - intervalWindow y (y + ℓ) t| / ℓ := by
    rw [normalizedIntervalWindow, normalizedIntervalWindow, ← sub_div, abs_div, abs_of_pos hℓ]
  simp_rw [heq]
  rw [integral_div]
  have h := div_le_div_of_nonneg_right (intervalWindow_translation_le 0 ℓ x y) hℓ.le
  simpa only [add_zero, div_mul_eq_mul_div] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelMixtureControl
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem kernelAverage_lipschitz {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) (C D : ℝ≥0)
    (hK : ∀ x, Integrable (K x) μ) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, ‖g t‖ ≤ C)
    (hmove : ∀ x y, (∫ t, |K x t - K y t| ∂μ) ≤ D * dist x y) :
    LipschitzWith (C * D) (kernelAverage μ K g) := by
  have hint (x) : Integrable (fun t => K x t * g t) μ :=
    (hK x).mul_bdd hg (Filter.Eventually.of_forall hgC)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, K x t * g t ∂μ) - ∫ t, K y t * g t ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hd : Integrable (fun t => |K x t - K y t|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hK x).sub (hK y)).norm
  have hpoint (t) : ‖K x t * g t - K y t * g t‖ ≤ (C : ℝ) * |K x t - K y t| := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hgC t) (abs_nonneg (K x t - K y t))
  have h := norm_integral_le_of_norm_le (hd.const_mul (C : ℝ)) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at h
  rw [Real.norm_eq_abs] at h
  apply h.trans
  have hbound := mul_le_mul_of_nonneg_left (hmove x y) C.coe_nonneg
  simpa only [NNReal.coe_mul, mul_assoc] using hbound

theorem kernelAverage_nonneg {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ)
    (hK : ∀ x t, 0 ≤ K x t) (hg : ∀ t, 0 ≤ g t) (x : X) :
    0 ≤ kernelAverage μ K g x := integral_nonneg (fun t => mul_nonneg (hK x t) (hg t))

theorem kernelAverage_cap {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) {C : ℝ}
    (hK : ∀ x, Integrable (K x) μ) (hK0 : ∀ x t, 0 ≤ K x t)
    (hmass : ∀ x, (∫ t, K x t ∂μ) = 1) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : X) :
    kernelAverage μ K g x ≤ C := by
  have hnorm (t) : ‖g t‖ ≤ C := by simpa only [Real.norm_of_nonneg (hgC t).1] using (hgC t).2
  have hint : Integrable (fun t => K x t * g t) μ := (hK x).mul_bdd hg (Filter.Eventually.of_forall hnorm)
  have h := integral_mono hint ((hK x).mul_const C)
    (fun t => mul_le_mul_of_nonneg_left (hgC t).2 (hK0 x t))
  simpa only [kernelAverage, integral_mul_const, hmass, one_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem integral_density_overlap (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hfmass : (∫ x, f x) = 1) (hgmass : (∫ x, g x) = 1) :
    (∫ x, |f x - g x|) = 2 - 2 * ∫ x, min (f x) (g x) := by
  have hm : Integrable (fun x => min (f x) (g x)) := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) := hf.add hg
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg, integral_const_mul,
    hfmass, hgmass]
  norm_num

theorem density_overlap_mass (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfmass : (∫ x, f x) = 1) :
    (∫ x, min (f x) (g x)) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)), ?_⟩
  have hm : Integrable (fun x => min (f x) (g x)) := hf.inf hg
  exact (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass

theorem product_density_l1_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hg : ∀ i, Integrable (g i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hfmass : ∀ i, (∫ x, f i x) = 1) (hgmass : ∀ i, (∫ x, g i x) = 1) :
    (∫ x : ι → ℝ, |(∏ i, f i (x i)) - ∏ i, g i (x i)|) ≤
      ∑ i, ∫ x, |f i x - g i x| := by
  let F : (ι → ℝ) → ℝ := fun x => ∏ i, f i (x i)
  let G : (ι → ℝ) → ℝ := fun x => ∏ i, g i (x i)
  let H : (ι → ℝ) → ℝ := fun x => ∏ i, min (f i (x i)) (g i (x i))
  let mass : ι → ℝ := fun i => ∫ x, min (f i x) (g i x)
  have hF : Integrable F := Integrable.fintype_prod hf
  have hG : Integrable G := Integrable.fintype_prod hg
  have hH : Integrable H := Integrable.fintype_prod (fun i => (hf i).inf (hg i))
  have hpoint (x : ι → ℝ) : |F x - G x| ≤ F x + G x - 2 * H x := by
    have hHF : H x ≤ F x := Finset.prod_le_prod
      (fun i _ => le_min (hf0 i _) (hg0 i _)) (fun i _ => min_le_left _ _)
    have hHG : H x ≤ G x := Finset.prod_le_prod
      (fun i _ => le_min (hf0 i _) (hg0 i _)) (fun i _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hmin := le_min hHF hHG
    linarith
  have hFmass : (∫ x, F x) = 1 := by
    dsimp only [F]
    rw [integral_fintype_prod_volume_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGmass : (∫ x, G x) = 1 := by
    dsimp only [G]
    rw [integral_fintype_prod_volume_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHmass : (∫ x, H x) = ∏ i, mass i := by
    exact integral_fintype_prod_volume_eq_prod (fun i x => min (f i x) (g i x))
  have hleft : Integrable (fun x => |F x - G x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hF.sub hG).norm
  have hsum : Integrable (fun x => F x + G x) := hF.add hG
  have hright : Integrable (fun x => F x + G x - 2 * H x) := hsum.sub (hH.const_mul 2)
  have hbound := integral_mono hleft hright hpoint
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFmass, hGmass, hHmass] at hbound
  have hm (i) : mass i ∈ Set.Icc (0 : ℝ) 1 :=
    density_overlap_mass (f i) (g i) (hf i) (hg i) (hf0 i) (hg0 i) (hfmass i)
  have hprod := one_sub_sum_le_positive_prod Finset.univ mass (fun i => 1 - mass i)
    (fun i _ => (hm i).1) (fun i _ => ⟨by linarith [(hm i).2], by linarith [(hm i).1]⟩)
    (fun i _ => by linarith)
  have herr : (∑ i, ∫ x, |f i x - g i x|) = 2 * ∑ i, (1 - mass i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_density_overlap (f i) (g i) (hf i) (hg i) (hfmass i) (hgmass i)]
    dsimp only [mass]
    ring
  rw [herr]
  change (∫ x, |F x - G x|) ≤ _
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxWindowAveraging
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_nonneg (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x t : ι → ℝ) :
    0 ≤ boxProbabilityWindow ℓ x t :=
  Finset.prod_nonneg (fun i _ => normalizedIntervalWindow_nonneg (hℓ i) _ _)

theorem boxProbabilityWindow_integrable (ℓ x : ι → ℝ) :
    Integrable (boxProbabilityWindow ℓ x) :=
  Integrable.fintype_prod (fun i => normalizedIntervalWindow_integrable (ℓ i) (x i))

theorem boxProbabilityWindow_measurable (ℓ x : ι → ℝ) : Measurable (boxProbabilityWindow ℓ x) := by
  apply Finset.measurable_prod
  intro i _
  exact (normalizedIntervalWindow_measurable _ _).comp (measurable_pi_apply i)

theorem boxProbabilityWindow_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x : ι → ℝ) :
    (∫ t, boxProbabilityWindow ℓ x t) = 1 := by
  unfold boxProbabilityWindow
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [normalizedIntervalWindow_mass (hℓ _), Finset.prod_const_one]

theorem boxProbabilityWindow_cap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t ≤ ∏ i, 1 / ℓ i :=
  Finset.prod_le_prod (fun i _ => normalizedIntervalWindow_nonneg (hℓ i) _ _)
    (fun i _ => normalizedIntervalWindow_le (hℓ i) _ _)

theorem boxProbabilityWindow_translation_le [DecidableEq ι]
    (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x y : ι → ℝ) :
    (∫ t, |boxProbabilityWindow ℓ x t - boxProbabilityWindow ℓ y t|) ≤
      (boxWindowTranslationBound ℓ hℓ : ℝ) * dist x y := by
  have h := product_density_l1_le_sum
    (fun i => normalizedIntervalWindow (ℓ i) (x i)) (fun i => normalizedIntervalWindow (ℓ i) (y i))
    (fun i => normalizedIntervalWindow_integrable _ _) (fun i => normalizedIntervalWindow_integrable _ _)
    (fun i => normalizedIntervalWindow_nonneg (hℓ i) _) (fun i => normalizedIntervalWindow_nonneg (hℓ i) _)
    (fun i => normalizedIntervalWindow_mass (hℓ i) _) (fun i => normalizedIntervalWindow_mass (hℓ i) _)
  apply h.trans
  change (∑ i, ∫ t, |normalizedIntervalWindow (ℓ i) (x i) t - normalizedIntervalWindow (ℓ i) (y i) t|) ≤
    (∑ i, 2 / ℓ i) * dist x y
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply (normalizedIntervalWindow_translation_le (hℓ i) (x i) (y i)).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (hℓ i).le)
  simpa only [Real.dist_eq] using dist_le_pi_dist x y i

theorem boxAverage_lipschitz [DecidableEq ι] (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (g : (ι → ℝ) → ℝ) (C : ℝ≥0) (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ t, ‖g t‖ ≤ C) :
    LipschitzWith (C * boxWindowTranslationBound ℓ hℓ)
      (kernelAverage volume (boxProbabilityWindow ℓ) g) :=
  kernelAverage_lipschitz volume (boxProbabilityWindow ℓ) g C (boxWindowTranslationBound ℓ hℓ)
    (boxProbabilityWindow_integrable ℓ) hg hbound (boxProbabilityWindow_translation_le ℓ hℓ)

theorem boxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (g : (ι → ℝ) → ℝ) {C : ℝ} (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x ∈ Set.Icc (0 : ℝ) C :=
  ⟨kernelAverage_nonneg volume _ g (boxProbabilityWindow_nonneg ℓ hℓ) (fun t => (hbound t).1) x,
    kernelAverage_cap volume _ g (boxProbabilityWindow_integrable ℓ) (boxProbabilityWindow_nonneg ℓ hℓ)
      (boxProbabilityWindow_mass ℓ hℓ) hg hbound x⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBoxTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem normalizedIntervalWindow_translate (ℓ x t : ℝ) :
    normalizedIntervalWindow ℓ x t = normalizedIntervalWindow ℓ 0 (t - x) := by
  have hm : t ∈ Set.Ioc x (x + ℓ) ↔ t - x ∈ Set.Ioc 0 (0 + ℓ) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [normalizedIntervalWindow, intervalWindow, Set.indicator, hm]

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_translate (ℓ x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t = boxProbabilityWindow ℓ 0 (t - x) := by
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedIntervalWindow_translate _ _ _

theorem boxAverage_eq_translate (ℓ : ι → ℝ) (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x =
      ∫ u, boxProbabilityWindow ℓ 0 u * g (u + x) := by
  change (∫ t, boxProbabilityWindow ℓ x t * g t) = _
  rw [← integral_add_right_eq_self (fun t => boxProbabilityWindow ℓ x t * g t) x]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [boxProbabilityWindow_translate, add_sub_cancel_right]

theorem affineBoxAverage_eq (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x =
      kernelAverage volume (boxProbabilityWindow ℓ) (fun t => g (A t)) (A.symm x) := by
  rw [boxAverage_eq_translate]
  unfold affineBoxAverage
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [map_add, A.apply_symm_apply, ContinuousLinearEquiv.coe_coe, add_comm]

theorem affineBoxAverage_lipschitz [DecidableEq ι] (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) (C : ℝ≥0)
    (hg : Measurable g) (hbound : ∀ t, ‖g t‖ ≤ C) :
    LipschitzWith ((C * boxWindowTranslationBound ℓ hℓ) * ‖A.symm.toContinuousLinearMap‖₊)
      (affineBoxAverage ℓ A.toContinuousLinearMap g) := by
  have h := (boxAverage_lipschitz ℓ hℓ (fun t => g (A t)) C
    (hg.comp A.continuous.measurable).aestronglyMeasurable (fun t => hbound (A t))).comp
      A.symm.toContinuousLinearMap.lipschitz
  have heq : (fun x => kernelAverage volume (boxProbabilityWindow ℓ)
      (fun t => g (A t)) (A.symm.toContinuousLinearMap x)) =
      affineBoxAverage ℓ A.toContinuousLinearMap g := by
    funext x
    exact (affineBoxAverage_eq ℓ A g x).symm
  change LipschitzWith _ (fun x => kernelAverage volume (boxProbabilityWindow ℓ)
    (fun t => g (A t)) (A.symm.toContinuousLinearMap x)) at h
  rw [heq] at h
  exact h

theorem affineBoxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) {C : ℝ}
    (hg : Measurable g) (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x ∈ Set.Icc (0 : ℝ) C := by
  rw [affineBoxAverage_eq]
  exact boxAverage_mem_Icc ℓ hℓ _ (hg.comp A.continuous.measurable).aestronglyMeasurable
    (fun t => hbound (A t)) _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem affineBoxIntegrand_integrable (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) (hgi : Integrable g) :
    Integrable (affineBoxIntegrand ℓ A g) (volume.prod volume) := by
  have hm : Measurable (affineBoxIntegrand ℓ A g) :=
    ((boxProbabilityWindow_measurable ℓ 0).comp measurable_snd).mul
      (hg.comp (measurable_fst.add (A.continuous.measurable.comp measurable_snd)))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with u
    exact (hgi.comp_add_right (A u)).const_mul (boxProbabilityWindow ℓ 0 u)
  · have heq (u : ι → ℝ) : (∫ x, ‖affineBoxIntegrand ℓ A g (x, u)‖) =
        ‖boxProbabilityWindow ℓ 0 u‖ * ∫ x, ‖g x‖ := by
      simp only [affineBoxIntegrand, norm_mul]
      rw [integral_const_mul, integral_add_right_eq_self (fun x => ‖g x‖) (A u)]
    simp_rw [heq]
    exact (boxProbabilityWindow_integrable ℓ 0).norm.mul_const _

theorem affineBoxAverage_integrable (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) (hgi : Integrable g) :
    Integrable (affineBoxAverage ℓ A g) :=
  (affineBoxIntegrand_integrable ℓ A g hg hgi).integral_prod_left

theorem affineBoxAverage_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ)
    (hg : Measurable g) (hgi : Integrable g) :
    (∫ x, affineBoxAverage ℓ A g x) = ∫ x, g x := by
  have hi : Integrable (Function.uncurry
      (fun x u => boxProbabilityWindow ℓ 0 u * g (x + A u))) (volume.prod volume) :=
    affineBoxIntegrand_integrable ℓ A g hg hgi
  change (∫ x, ∫ u, boxProbabilityWindow ℓ 0 u * g (x + A u)) = _
  rw [integral_integral_swap hi]
  simp_rw [integral_const_mul, integral_add_right_eq_self]
  rw [integral_mul_const, boxProbabilityWindow_mass ℓ hℓ 0, one_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

theorem integral_comp_inverse_linear (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) :
    (∫ x, f (A.symm x)) = (inverseJacobian A)⁻¹ * ∫ x, f x := by
  have h := A.symm.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [inverse_map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (inverseJacobian_pos A).le)] at h
  exact h.symm

theorem linearDensityPullback_measurable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (linearDensityPullback A f) :=
  measurable_const.mul (hf.comp A.symm.continuous.measurable)

omit [Fintype ι] in
theorem linearDensityPullback_nonneg (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ linearDensityPullback A f x := mul_nonneg (inverseJacobian_pos A).le (hf _)

theorem linearDensityPullback_integrable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (linearDensityPullback A f) := by
  have hm : Integrable f (Measure.map A.symm volume) := by
    rw [inverse_map_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (A.symm.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hm).const_mul _

theorem linearDensityPullback_integral (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) : (∫ x, linearDensityPullback A f x) = ∫ x, f x := by
  unfold linearDensityPullback
  rw [integral_const_mul, integral_comp_inverse_linear, ← mul_assoc,
    mul_inv_cancel₀ (inverseJacobian_pos A).ne', one_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem linearBoxDensity_measurable (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measurable (linearBoxDensity ℓ A) :=
  linearDensityPullback_measurable A (boxProbabilityWindow_measurable ℓ 0)

theorem linearBoxDensity_integrable (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Integrable (linearBoxDensity ℓ A) :=
  linearDensityPullback_integrable A (boxProbabilityWindow_integrable ℓ 0)

theorem linearBoxDensity_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (∫ x, linearBoxDensity ℓ A x) = 1 := by
  unfold linearBoxDensity
  rw [linearDensityPullback_integral, boxProbabilityWindow_mass ℓ hℓ]

theorem linearBoxDensity_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    linearBoxDensity ℓ A x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap ℓ hℓ A) :=
  ⟨linearDensityPullback_nonneg A (boxProbabilityWindow_nonneg ℓ hℓ 0) x,
    mul_le_mul_of_nonneg_left (boxProbabilityWindow_cap ℓ hℓ 0 (A.symm x))
      (inverseJacobian_pos A).le⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TwoBoxSmoothingComplex
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem twoBoxDifferenceDensity_mem_Icc (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    twoBoxDifferenceDensity ℓ r A B x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap r hr B) :=
  affineBoxAverage_mem_Icc ℓ hℓ A _ (linearBoxDensity_measurable r B)
    (linearBoxDensity_mem_Icc r hr B) x

theorem twoBoxDifferenceDensity_lipschitz [DecidableEq ι] (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    LipschitzWith ((linearBoxDensityCap r hr B * boxWindowTranslationBound ℓ hℓ) *
      ‖A.symm.toContinuousLinearMap‖₊) (twoBoxDifferenceDensity ℓ r A B) := by
  apply affineBoxAverage_lipschitz ℓ hℓ A _ _ (linearBoxDensity_measurable r B)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (linearBoxDensity_mem_Icc r hr B x).1]
  exact (linearBoxDensity_mem_Icc r hr B x).2

theorem twoBoxDifferenceDensity_integrable (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : Integrable (twoBoxDifferenceDensity ℓ r A B) :=
  affineBoxAverage_integrable ℓ A.toContinuousLinearMap _
    (linearBoxDensity_measurable r B) (linearBoxDensity_integrable r B)

theorem twoBoxDifferenceDensity_mass (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (∫ x, twoBoxDifferenceDensity ℓ r A B x) = 1 := by
  unfold twoBoxDifferenceDensity
  rw [affineBoxAverage_mass ℓ hℓ _ _ (linearBoxDensity_measurable r B)
    (linearBoxDensity_integrable r B), linearBoxDensity_mass r hr]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

theorem fixedSpatialBlockKernel_lipschitz
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    LipschitzWith (fixedSpatialBlockDensityLipschitz A B)
      (twoBoxDifferenceDensity (fun _ => 1) (fun _ => 1)
        (A.trans (ContinuousLinearEquiv.neg ℝ)) B) :=
  twoBoxDifferenceDensity_lipschitz _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _

theorem fixedSpatialBlockDensity_probability_density
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (∀ x, 0 ≤ fixedSpatialBlockDensity μ center rest A B x) ∧
      Integrable (fixedSpatialBlockDensity μ center rest A B) ∧
      (∫ x, fixedSpatialBlockDensity μ center rest A B x) = 1 := by
  apply haarShiftDensity_probability volume μ (measurable_const.add hrest)
    (fixedSpatialBlockKernel_lipschitz A B).continuous.measurable
    (twoBoxDifferenceDensity_integrable _ _ _ _)
  · intro x
    exact (twoBoxDifferenceDensity_mem_Icc _ _ (fun _ => zero_lt_one)
      (fun _ => zero_lt_one) _ _ x).1
  · exact twoBoxDifferenceDensity_mass _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X]

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

end TopPart

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

variable [DecidableEq G]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

omit [Fintype G] [Fintype X] in
theorem fixedSpatialKernelRest_measurable (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) :
    Measurable (fixedSpatialKernelRest e W L z) := by
  unfold fixedSpatialKernelRest
  fun_prop

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

variable {T : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G]

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

omit [Fintype G] in
theorem fixedSpatialKernelDensity_probability_density :
    (∀ x, 0 ≤ fixedSpatialKernelDensity e W L z h0 h1 x) ∧
      Integrable (fixedSpatialKernelDensity e W L z h0 h1) ∧
      (∫ x, fixedSpatialKernelDensity e W L z h0 h1 x) = 1 :=
  fixedSpatialBlockDensity_probability_density (unitBoxMeasure T) _
    (fixedSpatialKernelRest_measurable e W L z) _ _

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

variable {T : Type*} [Fintype T] [DecidableEq X]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lower width : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hw : ∀ g, width g ≠ 0)

local notation "density" => fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualSlicedNumericsRecoveredBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
theorem actualSlicedForecastDensityBudget_ge_one (v : ℝ) :
    1 ≤ actualSlicedForecastDensityBudget s v := by
  apply Real.one_le_exp_iff.mpr
  unfold forecastOriginalSmoothBudget
  positivity

namespace ActualFixedSpatialSlicedForecastNumerics

variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

omit [DecidableEq X] in

theorem joint_density_grid_cap_le_exp :
    s.κ * actualSlicedForecastDensityBudget s qnum.v * qnum.Ctail ^ Fintype.card A ≤
      Real.exp qnum.capLog := by
  have hbase : 0 ≤ s.κ * actualSlicedForecastDensityBudget s qnum.v *
      qnum.Ctail ^ Fintype.card A :=
    mul_nonneg (mul_nonneg s.hκ (Real.exp_nonneg _)) (pow_nonneg qnum.hCtail _)
  have hdecay : 0 ≤ actualSlicedForecastDecayBudget s := Real.exp_nonneg _
  apply le_trans _ qnum.hcap
  nlinarith

omit [DecidableEq X] in

theorem spatial_inverse_factor_le_exp : 8 / τ ≤ Real.exp qnum.Pnative := by
  have hD := actualSlicedForecastDensityBudget_ge_one s qnum.v
  have htail : 0 ≤ (Fintype.card A : ℝ) * (qnum.Lt : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) qnum.Lt.coe_nonneg
  have hmax : 0 ≤ max (8 / τ) 1 := zero_le_one.trans (le_max_right _ _)
  calc
    _ ≤ max (8 / τ) 1 := le_max_left _ _
    _ ≤ (actualSlicedForecastDensityBudget s qnum.v +
        (Fintype.card A : ℝ) * (qnum.Lt : ℝ)) * max (8 / τ) 1 := by nlinarith
    _ ≤ _ := qnum.hfactor

end ActualFixedSpatialSlicedForecastNumerics
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedInactiveGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)


variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

omit [Fintype Tsp] in

theorem inactive_grid_mass_le
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
          slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ Ctail ^ Fintype.card A := by
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hc := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U b hR hσ S slice.path.sample slice.path.hs
  rw [slice.principalLaw_eq_contained]
  exact forecastInactive_sliced_fixed_grid_mass_le_v2 B U b hR hσ S
    slice.principalLength slice.principalStep slice.principalStart slice.principalLength_pos
    slice.principalSupport selected s.hselected δ Ptail Hchild hδ hreg s.hsmall hgrid
    (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) hc
    s.L s.hL hPtail (s.hprimitiveCap.trans hsPtail) hstrideTail s.hB
    Ctail hCtail htailactual slice.path.commonTuple z

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedNumericalGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

omit [Fintype Tsp] in

theorem inactive_grid_mass_le (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      member.slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected member.slice.path.sample)
          member.slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ qnum.Ctail ^ Fintype.card A := by
  exact member.slice.inactive_grid_mass_le s qnum.δ qnum.Hchild qnum.hδ member.regular
    qnum.Ptail qnum.Ctail qnum.hPtail qnum.hprimitive member.stride qnum.hCtail qnum.htailactual z

end ActualFixedSpatialSlicedAdmissiblePath

namespace ActualFixedSpatialForecastPath

variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedNumericalDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem SlicedProductBlock.pairDensity_nonneg {ι : Type*} [Fintype ι]
    (A B : SlicedProductBlock ι) (x : ℝ) : 0 ≤ SlicedProductBlock.pairDensity A B x := by
  unfold pairDensity affinePairDensity randomIntervalDensity densityMixture
  apply integral_nonneg
  intro p
  unfold normalizedIntervalWindow affinePairWidth
  exact div_nonneg (intervalWindow_mem_Icc _ _ _).1
    (le_max_of_le_left (abs_nonneg _))

theorem SlicedProductBlock.fourDensity_nonneg {ι : Type*} [Fintype ι]
    (A B C D : SlicedProductBlock ι) (x : ℝ) :
    0 ≤ SlicedProductBlock.fourDensity A B C D x := by
  unfold fourDensity scalarDensityConvolution
  exact integral_nonneg (fun t =>
    mul_nonneg (pairDensity_nonneg A B _) (pairDensity_nonneg C D _))

theorem principalFourRemainderDensity_nonneg {J ι : Type*}
    [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]
    (c : Fin 4 ⊕ J → ℝ) (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) (x : ℝ) :
    0 ≤ principalFourRemainderDensity c lower width x := by
  unfold principalFourRemainderDensity independentShiftDensity densityMixture
  exact integral_nonneg (fun t => SlicedProductBlock.fourDensity_nonneg _ _ _ _ _)

theorem canonicalSlicedPrincipalDensity_nonneg {B F : Type*}
    [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ)
    (lower width : B × F → ℝ) (x : ℝ) :
    0 ≤ canonicalSlicedPrincipalDensity hB i c lower width x :=
  principalFourRemainderDensity_nonneg _ _ _ _

theorem jointSlicedPrincipalDensity_nonneg {D : Type*} [Fintype D]
    {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (shift : D → ℝ) (y : (Σ _d : D, Unit) → ℝ) :
    0 ≤ jointSlicedPrincipalDensity hB i c lower width shift y := by
  exact sigmaAxisWeight_nonneg _
    (fun d v => canonicalSlicedPrincipalDensity_nonneg (hB d) (i d)
      (c d) (lower d) (width d) _) y

end Erdos3

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

theorem density_nonneg
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    0 ≤ slice.density hBactive y := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  classical
  unfold density fixedSpatialKernelSliceOriginalForecastDensity
    fixedSpatialKernelOriginalForecastDensity binaryDensity allocatedFixedPathLiftDensity
  apply mul_nonneg
  · exact (fixedSpatialKernelDensity_probability_density _ _ _ _ _ _).1 _
  · exact jointSlicedPrincipalDensity_nonneg _ _ _ _ _ _ _

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

theorem density_mem_Icc
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    member.slice.density s.hBactive y ∈
      Set.Icc (0 : ℝ) (actualSlicedForecastDensityBudget s qnum.v) := by
  have hbound := (member.slice.density_uniform_budget s.hBactive s.hP s.hδslice
    s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks qnum.hv member.kernelWidth).2.2.1 y
  have hn := member.slice.density_nonneg s.hBactive y
  rw [Real.norm_eq_abs, abs_of_nonneg hn] at hbound
  exact ⟨hn, hbound⟩

theorem density_lipschitz :
    LipschitzWith (Real.toNNReal (actualSlicedForecastDensityBudget s qnum.v))
      (member.slice.density s.hBactive) :=
  (member.slice.density_uniform_budget s.hBactive s.hP s.hδslice
    s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks qnum.hv member.kernelWidth).2.2.2

theorem density_lipschitz_nnreal :
    LipschitzWith
      (⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩ : ℝ≥0)
      (member.slice.density s.hBactive) := by
  have hbudget : Real.toNNReal (actualSlicedForecastDensityBudget s qnum.v) =
      (⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩ : ℝ≥0) := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (Real.exp_nonneg _)
  rw [← hbudget]
  exact member.density_lipschitz s qnum

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialNumericalPatchEndpoint
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_numerical_retained_forecast_score_oai
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    {degree r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ degree) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) degree E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (member.slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hr : (r : ℝ) ≤ budget) (hE : (E : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hKbudget : (K : ℝ) ≤ Real.exp budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hqbudget : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let D : ℝ≥0 := ⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩
  let Icap : ℝ≥0 := ⟨qnum.Ctail ^ Fintype.card A, pow_nonneg qnum.hCtail _⟩
  have hN (i : X) : 0 < physicalN i := Nat.cast_pos.mp
    ((Real.exp_pos (spatialPatchExtractionCost (recoveredKernelScalarBudget budget))).trans_le
      (hlarge i))
  have hXnat : Fintype.card X ≤ Dmod :=
    (Nat.le_add_right (Fintype.card X) _).trans s.hDmod
  have hX : (Fintype.card X : ℝ) ≤ budget := (Nat.cast_le.mpr hXnat).trans hDmodBudget
  have hOutNat : Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) ≤ Dmod := by
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
      s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hOut : (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) : ℝ) ≤ budget :=
    (Nat.cast_le.mpr hOutNat).trans hDmodBudget
  exact member.slice.relativePatchSliceConclusion_of_primitive_retained_forecast_score
    selected s.hBactive o bW hb e s.hm s.hDmod cutoff hcutoff hsmall ⟨s.κ, s.hκ⟩
    poly hm hN w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight hcoords hcol hdiv
    D Icap (member.density_mem_Icc s qnum) (member.density_lipschitz_nnreal s qnum)
    (member.inactive_grid_mass_le s qnum) s.forward s.hforward s.K s.hK s.hτ f hf
    hlam hδ haccuracy hε hdiscount hscore hbudget hr hE hX hOut
    hKbudget hχbudget hBbudget
    ((qnum.joint_density_grid_cap_le_exp s).trans (Real.exp_le_exp.mpr hcapLog))
    hqbudget (qnum.hcoord.trans (Real.exp_le_exp.mpr hPnative))
    ((qnum.spatial_inverse_factor_le_exp s).trans (Real.exp_le_exp.mpr hPnative))
    hscoreLower hlarge hrank

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_oai
