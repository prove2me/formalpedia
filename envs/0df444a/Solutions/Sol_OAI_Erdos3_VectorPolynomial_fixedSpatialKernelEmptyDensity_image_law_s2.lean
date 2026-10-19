-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:17:13.059627+00:00
-- url     : https://prove2.me/submissions/f0bb567a-c547-4ef8-8cef-d3451ddeec9d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_twoBoxDifferenceDensity_mem_Icc_s2

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

private theorem interval_separation {a b c d t : ℝ} (hs : t ∈ Ioc a b) (ht : t ∉ Ioc c d) :
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

theorem affineBoxAverage_test_integral (ℓ : ι → ℝ)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g φ : (ι → ℝ) → ℝ)
    (hg : Measurable g) (hgi : Integrable g) (hφ : Measurable φ)
    {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, affineBoxAverage ℓ A g x * φ x) =
      ∫ u, boxProbabilityWindow ℓ 0 u * ∫ y, g y * φ (y - A u) := by
  have hi : Integrable (Function.uncurry
      (fun x u => (boxProbabilityWindow ℓ 0 u * g (x + A u)) * φ x))
      (volume.prod volume) :=
    (affineBoxIntegrand_integrable ℓ A g hg hgi).mul_bdd
      (hφ.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hφC p.1))
  calc
    (∫ x, affineBoxAverage ℓ A g x * φ x) =
        ∫ x, ∫ u, (boxProbabilityWindow ℓ 0 u * g (x + A u)) * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ u, ∫ x, (boxProbabilityWindow ℓ 0 u * g (x + A u)) * φ x :=
      integral_integral_swap hi
    _ = ∫ u, boxProbabilityWindow ℓ 0 u * ∫ y, g y * φ (y - A u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [mul_assoc, integral_const_mul]
      congr 1
      have h := integral_add_right_eq_self (μ := volume) (fun y => g y * φ (y - A u)) (A u)
      simpa only [add_sub_cancel_right] using h

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

theorem inverse_map_volume (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measure.map A.symm volume = ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    A.symm.toLinearEquiv.isUnit_det'.ne_zero
  simpa only [inverseJacobian, abs_inv, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

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

theorem linearDensityPullback_test_integral (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f φ : (ι → ℝ) → ℝ) :
    (∫ x, linearDensityPullback A f x * φ x) = ∫ u, f u * φ (A u) := by
  have heq (x : ι → ℝ) : linearDensityPullback A f x * φ x =
      linearDensityPullback A (fun u => f u * φ (A u)) x := by
    simp only [linearDensityPullback, A.apply_symm_apply, mul_assoc]
  simp_rw [heq]
  exact linearDensityPullback_integral A _

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

theorem twoBoxDifferenceDensity_test_integral (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (φ : (ι → ℝ) → ℝ)
    (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, twoBoxDifferenceDensity ℓ r A B x * φ x) =
      ∫ u, boxProbabilityWindow ℓ 0 u *
        ∫ v, boxProbabilityWindow r 0 v * φ (B v - A u) := by
  unfold twoBoxDifferenceDensity
  rw [affineBoxAverage_test_integral ℓ _ _ φ
    (linearBoxDensity_measurable r B) (linearBoxDensity_integrable r B) hφ hφC]
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  exact linearDensityPullback_test_integral B _ (fun y => φ (y - A u))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem positiveUnitBox_measurable : MeasurableSet (positiveUnitBox ι) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

theorem haarShiftDensity_measurable (ν : Measure T) [SFinite ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f) :
    Measurable (haarShiftDensity ν z f) := by
  have hm : Measurable (fun p : T × G => f (p.2 - z p.1)) :=
    hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

theorem haarShiftDensity_test_integral (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (φ : G → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, haarShiftDensity ν z f x * φ x ∂μ) =
      ∫ t, ∫ u, f u * φ (u + z t) ∂μ ∂ν := by
  have hi := densityMixture_joint_integrable ν μ (fun t x => f (x - z t))
    (hf.comp (measurable_snd.sub (hz.comp measurable_fst)))
    (ae_of_all ν (fun t => ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩))
  change (∫ x, densityMixture ν (fun t y => f (y - z t)) x * φ x ∂μ) = _
  rw [densityMixture_test_integral ν μ _ hi φ hφ hbound]
  apply integral_congr_ae
  exact ae_of_all ν (fun t => by
    have he := integral_add_right_eq_self (μ := μ) (fun x => f (x - z t) * φ x) (z t)
    simpa only [add_sub_cancel_right] using he.symm)

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
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

private theorem fixedSpatialBlockKernel_lipschitz
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    LipschitzWith (fixedSpatialBlockDensityLipschitz A B)
      (twoBoxDifferenceDensity (fun _ => 1) (fun _ => 1)
        (A.trans (ContinuousLinearEquiv.neg ℝ)) B) :=
  twoBoxDifferenceDensity_lipschitz _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _

theorem fixedSpatialBlockDensity_measurable
    (μ : Measure T) [SFinite μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    Measurable (fixedSpatialBlockDensity μ center rest A B) :=
  haarShiftDensity_measurable μ (measurable_const.add hrest)
    (fixedSpatialBlockKernel_lipschitz A B).continuous.measurable

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
    exact (twoBoxDifferenceDensity_mem_Icc_s2 _ _ (fun _ => zero_lt_one)
      (fun _ => zero_lt_one) _ _ x).1
  · exact twoBoxDifferenceDensity_mass _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _

theorem fixedSpatialBlockDensity_probability
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    IsProbabilityMeasure (realDensityMeasure volume (fixedSpatialBlockDensity μ center rest A B)) := by
  have hp := fixedSpatialBlockDensity_probability_density μ center hrest A B
  exact realDensityMeasure_probability volume _ hp.2.1 hp.1 hp.2.2

theorem fixedSpatialBlockDensity_real_test_integral
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (φ : (X → ℝ) → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, fixedSpatialBlockDensity μ center rest A B x * φ x) =
      ∫ t, ∫ u, boxProbabilityWindow (fun _ : X => 1) 0 u *
        ∫ v, boxProbabilityWindow (fun _ : X => 1) 0 v *
          φ (center + A u + B v + rest t) ∂volume ∂volume ∂μ := by
  have hf := fixedSpatialBlockKernel_lipschitz A B
  have hi := twoBoxDifferenceDensity_integrable (fun _ : X => 1) (fun _ => 1)
    (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  have h0 (x : X → ℝ) : 0 ≤ twoBoxDifferenceDensity (fun _ : X => 1) (fun _ => 1)
      (A.trans (ContinuousLinearEquiv.neg ℝ)) B x :=
    (twoBoxDifferenceDensity_mem_Icc_s2 _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _ x).1
  have hm := twoBoxDifferenceDensity_mass (fun _ : X => 1) (fun _ => 1)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  change (∫ x, haarShiftDensity μ (fun t => center + rest t) _ x * φ x) = _
  rw [haarShiftDensity_test_integral volume μ (z := fun t => center + rest t)
    (measurable_const.add hrest)
    hf.continuous.measurable hi h0 hm φ hφ hbound]
  apply integral_congr_ae
  exact ae_of_all μ (fun t => by
    have he (u v : X → ℝ) :
        B v - (A.trans (ContinuousLinearEquiv.neg ℝ)) u + (center + rest t) =
          center + A u + B v + rest t := by
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply,
        sub_neg_eq_add]
      abel
    simpa only [he] using twoBoxDifferenceDensity_test_integral (fun _ : X => 1)
      (fun _ => 1) (A.trans (ContinuousLinearEquiv.neg ℝ)) B
      (fun y => φ (y + (center + rest t)))
      (hφ.comp (measurable_id.add measurable_const)) (fun y => hbound _))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal

theorem boxProbabilityWindow_one_eq_indicator (X : Type*) [Fintype X] :
    boxProbabilityWindow (fun _ : X => 1) 0 =
      (positiveUnitBox X).indicator (fun _ => (1 : ℝ)) := by
  funext u
  by_cases hu : u ∈ positiveUnitBox X
  · rw [Set.indicator_of_mem hu]
    simp only [boxProbabilityWindow, normalizedIntervalWindow, Pi.zero_apply,
      zero_add, div_one, intervalWindow]
    simp only [Set.indicator_of_mem (hu _ (Set.mem_univ _)), Finset.prod_const_one]
  · rw [Set.indicator_of_notMem hu]
    have he : ∃ i, u i ∉ Set.Ioc (0 : ℝ) 1 := by
      simpa only [positiveUnitBox, Set.mem_pi, Set.mem_univ, forall_const, not_forall] using hu
    obtain ⟨i, hi⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [normalizedIntervalWindow, Pi.zero_apply, zero_add, div_one,
      intervalWindow, Set.indicator_of_notMem hi]

theorem unitBoxMeasure_eq_boxWindowDensity (X : Type*) [Fintype X] :
    unitBoxMeasure X = realDensityMeasure volume (boxProbabilityWindow (fun _ : X => 1) 0) := by
  rw [boxProbabilityWindow_one_eq_indicator]
  change volume.restrict (positiveUnitBox X) =
    volume.withDensity (fun u => ENNReal.ofReal ((positiveUnitBox X).indicator (fun _ => (1 : ℝ)) u))
  have he : (fun u => ENNReal.ofReal ((positiveUnitBox X).indicator (fun _ => (1 : ℝ)) u)) =
      (positiveUnitBox X).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext u
    by_cases hu : u ∈ positiveUnitBox X <;> simp [hu]
  rw [he]
  exact (withDensity_indicator_one (μ := volume) (positiveUnitBox_measurable (ι := X))).symm

theorem unitBoxMeasure_real_integral {X : Type*} [Fintype X] (φ : (X → ℝ) → ℝ) :
    (∫ u, φ u ∂unitBoxMeasure X) =
      ∫ u, boxProbabilityWindow (fun _ : X => 1) 0 u * φ u := by
  rw [unitBoxMeasure_eq_boxWindowDensity,
    realDensityMeasure_integral volume _ (boxProbabilityWindow_measurable _ _)
      (boxProbabilityWindow_nonneg _ (fun _ => zero_lt_one) _)]

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

theorem fixedSpatialBlockDensity_mapped_real_integral
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (φ : (X → ℝ) → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ p, φ (center + A p.2.1 + B p.2.2 + rest p.1)
      ∂μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))) =
        ∫ y, fixedSpatialBlockDensity μ center rest A B y * φ y := by
  have hmap : Measurable (fun p : T × ((X → ℝ) × (X → ℝ)) =>
      center + A p.2.1 + B p.2.2 + rest p.1) := by
    fun_prop
  have hi : Integrable (fun p => φ (center + A p.2.1 + B p.2.2 + rest p.1))
      (μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))) :=
    (integrable_const C).mono' (hφ.comp hmap).aestronglyMeasurable
      (ae_of_all _ (fun p => hbound _))
  rw [integral_prod _ hi, fixedSpatialBlockDensity_real_test_integral μ center hrest A B φ hφ hbound]
  apply integral_congr_ae
  filter_upwards [] with t
  have hit : Integrable (fun p : (X → ℝ) × (X → ℝ) =>
      φ (center + A p.1 + B p.2 + rest t)) ((unitBoxMeasure X).prod (unitBoxMeasure X)) :=
    (integrable_const C).mono'
      (hφ.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ (fun p => hbound _))
  rw [integral_prod _ hit, unitBoxMeasure_real_integral]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [unitBoxMeasure_real_integral]

theorem fixedSpatialBlockDensity_image_law
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).map
        (fun p => center + A p.2.1 + B p.2.2 + rest p.1) =
      realDensityMeasure volume (fixedSpatialBlockDensity μ center rest A B) := by
  let source := μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))
  let U := fun p : T × ((X → ℝ) × (X → ℝ)) => center + A p.2.1 + B p.2.2 + rest p.1
  have hU : Measurable U := by fun_prop
  let : IsProbabilityMeasure (source.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  let := fixedSpatialBlockDensity_probability μ center hrest A B
  change source.map U = _
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := fixedSpatialBlockDensity_mapped_real_integral μ center hrest A B
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  change (∫ p, s.indicator (fun _ => (1 : ℝ)) (U p) ∂source) = _ at ht
  rw [← integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable,
    ← realDensityMeasure_integral volume _ (fixedSpatialBlockDensity_measurable μ center hrest A B)
      (fixedSpatialBlockDensity_probability_density μ center hrest A B).1] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

variable [Fintype X]

theorem fixedSpatialEmptyCoordinates_measurePreserving :
    MeasurePreserving (fixedSpatialEmptyCoordinates (X := X)) volume volume := by
  have hp := volume_measurePreserving_piCongrLeft (fun _ : Σ _ : X, Unit ⊕ Empty => ℝ)
    (fixedSpatialEmptyIndex (X := X)).symm
  convert hp using 1
  funext u a
  rcases a with ⟨x, v | e⟩
  · cases v
    rfl
  · exact isEmptyElim e

theorem fixedSpatialEmptyDensity_image_law (f : (X → ℝ) → ℝ) :
    Measure.map fixedSpatialEmptyCoordinates (realDensityMeasure volume f) =
      realDensityMeasure volume (fixedSpatialEmptyDensity f) := by
  have h := realDensityMeasure_map_equiv
    (fixedSpatialEmptyCoordinates (X := X)).toHomeomorph.toMeasurableEquiv volume f
  change Measure.map (fixedSpatialEmptyCoordinates (X := X)) (realDensityMeasure volume f) =
    realDensityMeasure (Measure.map (fixedSpatialEmptyCoordinates (X := X)) volume)
      (fixedSpatialEmptyDensity f) at h
  rw [fixedSpatialEmptyCoordinates_measurePreserving.map_eq] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable (ι : Type*) [Fintype ι]

theorem unitBoxMeasure_eq_pi :
    unitBoxMeasure ι = Measure.pi (fun _ : ι => unitScalarMeasure) := by
  change (Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
    (Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1)) = _
  exact Measure.restrict_pi_pi _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem unitBoxMeasure_reindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e)
      (unitBoxMeasure I) (unitBoxMeasure J) := by
  simpa only [unitBoxMeasure_eq_pi] using
    measurePreserving_piCongrLeft (fun _ : J => unitScalarMeasure) e

theorem unitBoxMeasure_sum (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ))
      (unitBoxMeasure (I ⊕ J)) ((unitBoxMeasure I).prod (unitBoxMeasure J)) := by
  simpa only [unitBoxMeasure_eq_pi] using
    measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => unitScalarMeasure)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

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

theorem fixedSpatialKernelMap_blocks (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ)
    (u v : X → ℝ) (t : T → ℝ) (x : X) :
    fixedSpatialKernelMap W L z ((Sum.elim u (Sum.elim v t)) ∘ e) ⟨x, Sum.inl ()⟩ =
      z (none, x) + (fixedSpatialKernelBlock e W L z false).mulVec u x +
        (fixedSpatialKernelBlock e W L z true).mulVec v x +
        fixedSpatialKernelRest e W L z t x := by
  unfold fixedSpatialKernelMap
  rw [← e.symm.sum_comp]
  simp only [Function.comp_apply, Equiv.apply_symm_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  unfold fixedSpatialKernelBlock fixedSpatialKernelRest Matrix.mulVec dotProduct
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.mul_sum]
  simp only [mul_add, Finset.mul_sum, mul_assoc]
  ring

theorem fixedSpatialKernelMap_blocks_actual (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (t : G → ℝ) (x : X) :
    fixedSpatialKernelMap W L z t ⟨x, Sum.inl ()⟩ =
      z (none, x) + (fixedSpatialKernelBlock e W L z false).mulVec
          (fun i => t (e.symm (Sum.inl i))) x +
        (fixedSpatialKernelBlock e W L z true).mulVec
          (fun i => t (e.symm (Sum.inr (Sum.inl i)))) x +
        fixedSpatialKernelRest e W L z (fun j => t (e.symm (Sum.inr (Sum.inr j)))) x := by
  convert fixedSpatialKernelMap_blocks e W L z
    (fun i => t (e.symm (Sum.inl i))) (fun i => t (e.symm (Sum.inr (Sum.inl i))))
    (fun j => t (e.symm (Sum.inr (Sum.inr j)))) x using 1
  congr 1
  funext g
  simp only [Function.comp_apply]
  generalize he : e g = a
  have hg := congrArg e.symm he
  simp only [Equiv.symm_apply_apply] at hg
  subst g
  rcases a with i | (i | j) <;> rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

theorem fixedSpatialKernelBlockCoordinates_measurePreserving (e : G ≃ X ⊕ (X ⊕ T)) :
    MeasurePreserving (fixedSpatialKernelBlockCoordinates e) (unitBoxMeasure G)
      ((unitBoxMeasure T).prod ((unitBoxMeasure X).prod (unitBoxMeasure X))) := by
  let e' := e.trans (Equiv.sumAssoc X X T).symm
  have hr := (unitBoxMeasure_sum (X ⊕ X) T).comp (unitBoxMeasure_reindex e')
  have hp := ((unitBoxMeasure_sum X X).prod (MeasurePreserving.id (unitBoxMeasure T))).comp hr
  have hs := (Measure.measurePreserving_swap
    (μ := (unitBoxMeasure X).prod (unitBoxMeasure X)) (ν := unitBoxMeasure T)).comp hp
  convert hs using 1
  funext t
  ext j <;> simp [fixedSpatialKernelBlockCoordinates, e',
    MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

theorem fixedSpatialKernelBlockCoordinates_image_law (e : G ≃ X ⊕ (X ⊕ T)) :
    (unitBoxMeasure G).map (fixedSpatialKernelBlockCoordinates e) =
      (unitBoxMeasure T).prod ((unitBoxMeasure X).prod (unitBoxMeasure X)) :=
  (fixedSpatialKernelBlockCoordinates_measurePreserving e).map_eq

variable [DecidableEq X]

theorem fixedSpatialKernelMap_block_image_law (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ)
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (hA : ∀ u, A u = (fixedSpatialKernelBlock e W L z false).mulVec u)
    (hB : ∀ u, B u = (fixedSpatialKernelBlock e W L z true).mulVec u) :
    (unitBoxMeasure G).map (fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) =
      realDensityMeasure volume (fixedSpatialBlockDensity (unitBoxMeasure T)
        (fun x => z (none, x)) (fixedSpatialKernelRest e W L z) A B) := by
  have h := fixedSpatialBlockDensity_image_law (unitBoxMeasure T) (fun x => z (none, x))
    (fixedSpatialKernelRest_measurable e W L z) A B
  let F := fun p : (T → ℝ) × ((X → ℝ) × (X → ℝ)) =>
    (fun x => z (none, x)) + A p.2.1 + B p.2.2 + fixedSpatialKernelRest e W L z p.1
  have hF : Measurable F := by
    exact ((measurable_const.add (A.continuous.measurable.comp (measurable_fst.comp measurable_snd))).add
      (B.continuous.measurable.comp (measurable_snd.comp measurable_snd))).add
      ((fixedSpatialKernelRest_measurable e W L z).comp measurable_fst)
  change ((unitBoxMeasure T).prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).map F = _ at h
  rw [← fixedSpatialKernelBlockCoordinates_image_law e,
    Measure.map_map hF (fixedSpatialKernelBlockCoordinates_measurePreserving e).measurable] at h
  have he : F ∘ fixedSpatialKernelBlockCoordinates e =
      fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩ := by
    funext t x
    simp only [Function.comp_apply, F, fixedSpatialKernelBlockCoordinates, Pi.add_apply, hA, hB]
    exact (fixedSpatialKernelMap_blocks_actual e W L z t x).symm
  rw [he] at h
  exact h

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

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_apply (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) (t : X → ℝ) :
    fixedSpatialKernelBlockEquiv e W L z b h t =
      (fixedSpatialKernelBlock e W L z b).mulVec t :=
  congrArg (fun f : (X → ℝ) →L[ℝ] (X → ℝ) => f t)
    (fixedSpatialKernelBlockEquiv_coe e W L z b h)

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

theorem fixedSpatialKernelDensity_image_law :
    (unitBoxMeasure G).map (fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) =
      realDensityMeasure volume (fixedSpatialKernelDensity e W L z h0 h1) :=
  fixedSpatialKernelMap_block_image_law e W L z _ _
    (fixedSpatialKernelBlockEquiv_apply e W L z false h0)
    (fixedSpatialKernelBlockEquiv_apply e W L z true h1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "spatial" => fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1)

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

omit hR hσ in
theorem fixedSpatialKernelEmptyDensity_image_law_s2_oai :
    (unitBoxMeasure G).map (fixedSpatialKernelMap W L z) = realDensityMeasure volume spatial := by
  have he : fixedSpatialKernelMap W L z =
      fixedSpatialEmptyCoordinates ∘ (fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) := rfl
  have hm : Measurable (fun t : G → ℝ => fun x : X =>
      fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) :=
    by unfold fixedSpatialKernelMap; fun_prop
  rw [he, ← Measure.map_map fixedSpatialEmptyCoordinates.continuous.measurable hm]
  rw [fixedSpatialKernelDensity_image_law e W L z h0 h1, fixedSpatialEmptyDensity_image_law]

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.VectorPolynomial.fixedSpatialKernelEmptyDensity_image_law_s2_oai.{u_1, u_2, u_3}
