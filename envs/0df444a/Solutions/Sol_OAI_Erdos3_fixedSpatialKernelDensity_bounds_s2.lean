-- Prove2me | solution 1 for OAI.Erdos3.fixedSpatialKernelDensity_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:41:36.510973+00:00
-- url     : https://prove2.me/submissions/13fb00b1-d47f-4290-9623-e73318815f96

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B082
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

theorem linearDensityPullback_measurable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (linearDensityPullback A f) :=
  measurable_const.mul (hf.comp A.symm.continuous.measurable)

omit [Fintype ι] in
theorem linearDensityPullback_nonneg (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ linearDensityPullback A f x := mul_nonneg (inverseJacobian_pos A).le (hf _)

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
open scoped NNReal

theorem densityMixture_section_integrable {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ C t) (x : X) :
    Integrable (fun t => F t x) μ :=
  hC.mono' (hm x) (hbound.mono (fun _ ht => ht x))

theorem densityMixture_cap {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, F t x ∈ Set.Icc (0 : ℝ) (C t)) (x : X) :
    densityMixture μ F x ∈ Set.Icc (0 : ℝ) (∫ t, C t ∂μ) := by
  have hb : ∀ᵐ t ∂μ, ∀ y, ‖F t y‖ ≤ C t := hbound.mono fun t ht y => by
    rw [Real.norm_of_nonneg (ht y).1]
    exact (ht y).2
  exact ⟨integral_nonneg_of_ae (hbound.mono (fun _ ht => (ht x).1)),
    integral_mono_ae (densityMixture_section_integrable μ F C hC hm hb x) hC
      (hbound.mono (fun _ ht => (ht x).2))⟩

theorem densityMixture_lipschitz {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) (F : T → X → ℝ) (L : T → ℝ≥0)
    (hL : Integrable (fun t => (L t : ℝ)) μ)
    (hint : ∀ x, Integrable (fun t => F t x) μ)
    (hLip : ∀ᵐ t ∂μ, LipschitzWith (L t) (F t)) :
    LipschitzWith ⟨∫ t, (L t : ℝ) ∂μ, integral_nonneg (fun t => (L t).coe_nonneg)⟩
      (densityMixture μ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, F t x ∂μ) - ∫ t, F t y ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hb : ∀ᵐ t ∂μ, ‖F t x - F t y‖ ≤ (L t : ℝ) * dist x y := by
    filter_upwards [hLip] with t ht
    simpa only [Real.dist_eq, Real.norm_eq_abs] using ht.dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hL.mul_const (dist x y)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_uniform_bound {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) [IsProbabilityMeasure μ] (F : T → X → ℝ) (C L : ℝ≥0)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hF : ∀ᵐ t ∂μ, (∀ x, F t x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (F t)) :
    (∀ x, densityMixture μ F x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (densityMixture μ F) := by
  have hb : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ (C : ℝ) := by
    filter_upwards [hF] with t ht
    intro x
    rw [Real.norm_of_nonneg (ht.1 x).1]
    exact (ht.1 x).2
  have hi := densityMixture_section_integrable μ F (fun _ => (C : ℝ)) (integrable_const _) hm hb
  constructor
  · intro x
    have h := densityMixture_cap μ F (fun _ => (C : ℝ)) (integrable_const _) hm
      (hF.mono (fun _ ht => ht.1)) x
    simpa only [integral_const, probReal_univ, one_smul] using h
  · have h := densityMixture_lipschitz μ F (fun _ => L) (integrable_const _) hi
      (hF.mono (fun _ ht => ht.2))
    have heq : (⟨∫ _ : T, (L : ℝ) ∂μ, integral_nonneg (fun _ => L.coe_nonneg)⟩ : ℝ≥0) = L := by
      apply Subtype.ext
      simp
    rw [heq] at h
    exact h

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

theorem fixedSpatialBlockDensity_bounds
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (∀ x, fixedSpatialBlockDensity μ center rest A B x ∈
      Set.Icc (0 : ℝ) (fixedSpatialBlockDensityCap B)) ∧
      LipschitzWith (fixedSpatialBlockDensityLipschitz A B)
        (fixedSpatialBlockDensity μ center rest A B) := by
  let f := twoBoxDifferenceDensity (fun _ : X => 1) (fun _ => 1)
    (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  have hf : LipschitzWith (fixedSpatialBlockDensityLipschitz A B) f :=
    fixedSpatialBlockKernel_lipschitz A B
  have hc (x : X → ℝ) : f x ∈ Set.Icc (0 : ℝ) (fixedSpatialBlockDensityCap B) :=
    twoBoxDifferenceDensity_mem_Icc_s2 _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _ x
  apply densityMixture_uniform_bound μ (fun t x => f (x - (center + rest t)))
    (fixedSpatialBlockDensityCap B) (fixedSpatialBlockDensityLipschitz A B)
  · intro x
    exact (hf.continuous.measurable.comp
      (measurable_const.sub (measurable_const.add hrest))).aestronglyMeasurable
  · exact ae_of_all μ (fun t => ⟨fun x => hc _, by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_sub_right] using hf.dist_le_mul
        (x - (center + rest t)) (y - (center + rest t))⟩)

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
theorem fixedSpatialKernelDensity_bounds_s2_oai :
    (∀ x, fixedSpatialKernelDensity e W L z h0 h1 x ∈ Set.Icc (0 : ℝ)
      (fixedSpatialBlockDensityCap (fixedSpatialKernelBlockEquiv e W L z true h1))) ∧
      LipschitzWith (fixedSpatialBlockDensityLipschitz
        (fixedSpatialKernelBlockEquiv e W L z false h0)
        (fixedSpatialKernelBlockEquiv e W L z true h1))
        (fixedSpatialKernelDensity e W L z h0 h1) :=
  fixedSpatialBlockDensity_bounds (unitBoxMeasure T) _
    (fixedSpatialKernelRest_measurable e W L z) _ _

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.fixedSpatialKernelDensity_bounds_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.fixedSpatialKernelDensity_bounds_s2_oai.{u_1, u_2, u_3}
