-- Prove2me | solution 1 for OAI.Erdos3.cutoff_box_image_comparison_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:23:16.135005+00:00
-- url     : https://prove2.me/submissions/ce41ad8c-7388-4ba4-84d4-dd40f6cc4a25

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

theorem intervalWindow_mem_Icc (a b t : ℝ) : intervalWindow a b t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ioc a b <;> simp [intervalWindow, ht]

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

theorem normalizedIntervalWindow_integrable (ℓ x : ℝ) :
    Integrable (normalizedIntervalWindow ℓ x) := (intervalWindow_integrable _ _).div_const ℓ

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

theorem boxProbabilityWindow_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x : ι → ℝ) :
    (∫ t, boxProbabilityWindow ℓ x t) = 1 := by
  unfold boxProbabilityWindow
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [normalizedIntervalWindow_mass (hℓ _), Finset.prod_const_one]

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxTestSmoothing
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem boxTestAverage_translate (δ : ℝ) (φ : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    boxTestAverage δ φ x = ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * φ (x + u) := by
  rw [boxTestAverage, boxAverage_eq_translate]
  simp only [add_comm]

theorem boxTestLipschitz_coe (δ : ℝ) (hδ : 0 < δ) :
    (boxTestLipschitz (ι := ι) δ hδ : ℝ) = 2 * Fintype.card ι / δ := by
  change (∑ _ : ι, 2 / δ) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem boxTestAverage_lipschitz [DecidableEq ι] (δ : ℝ) (hδ : 0 < δ)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (boxTestLipschitz (ι := ι) δ hδ) (boxTestAverage δ φ) := by
  have h := boxAverage_lipschitz (fun _ : ι => δ) (fun _ => hδ) φ 1
    hφ.aestronglyMeasurable hbound
  simp only [one_mul] at h
  exact h

theorem boxTestAverage_norm_le (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) (x : ι → ℝ) : ‖boxTestAverage δ φ x‖ ≤ 1 := by
  have hp (t : ι → ℝ) : ‖boxProbabilityWindow (fun _ => δ) x t * φ t‖ ≤
      boxProbabilityWindow (fun _ => δ) x t := by
    rw [norm_mul, Real.norm_of_nonneg (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _)]
    exact (mul_le_mul_of_nonneg_left (hbound t)
      (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le (boxProbabilityWindow_integrable (fun _ => δ) x)
    (Filter.Eventually.of_forall hp)
  exact h.trans_eq (boxProbabilityWindow_mass _ (fun _ => hδ) x)

theorem boxProbabilityWindow_support_dist (δ : ℝ) (hδ : 0 < δ) (u : ι → ℝ)
    (hu : boxProbabilityWindow (fun _ => δ) 0 u ≠ 0) : dist u 0 ≤ δ := by
  apply (dist_pi_le_iff hδ.le).mpr
  intro i
  have hi : normalizedIntervalWindow δ 0 (u i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hu i (Finset.mem_univ i)
  have hui : u i ∈ Set.Ioc (0 : ℝ) δ := by
    by_contra hnot
    apply hi
    simp only [normalizedIntervalWindow, intervalWindow, zero_add, Set.indicator_of_notMem hnot, zero_div]
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_pos hui.1] using hui.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothedImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mappedTest_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (hU : Measurable U)
    (φ : X → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    Integrable (fun a => φ (U a)) μ :=
  (integrable_const (1 : ℝ)).mono' (hφ.comp hU).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => hbound (U a)))

theorem mappedTest_norm_le {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (φ : X → ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) : ‖mappedTest μ U φ‖ ≤ μ.real Set.univ := by
  have h := norm_integral_le_of_norm_le (integrable_const (1 : ℝ) (μ := μ))
    (Filter.Eventually.of_forall (fun a => hbound (U a)))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  exact h

theorem mappedTest_shift_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [SFinite μ] (U : Ω → (ι → ℝ)) (hU : Measurable U)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) :
    Measurable (fun z => mappedTest μ U (fun x => φ (x + z))) := by
  have hm : Measurable (fun p : Ω × (ι → ℝ) => φ (U p.1 + p.2)) :=
    hφ.comp ((hU.comp measurable_fst).add measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem coupled_mappedTest_difference {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hmass : μ.real Set.univ ≤ 1)
    (U V : Ω → X) (hU : Measurable U) (hV : Measurable V)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ᵐ a ∂μ, dist (U a) (V a) ≤ ε)
    (φ : X → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L φ) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤ L * ε := by
  have hiU := mappedTest_integrable μ U hU φ hφ hbound
  have hiV := mappedTest_integrable μ V hV φ hφ hbound
  have hp : ∀ᵐ a ∂μ, ‖φ (U a) - φ (V a)‖ ≤ (L : ℝ) * ε := by
    filter_upwards [hclose] with a ha
    have h := (hL.dist_le_mul (U a) (V a)).trans (mul_le_mul_of_nonneg_left ha L.coe_nonneg)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using h
  have h := norm_integral_le_of_norm_le (integrable_const ((L : ℝ) * ε) (μ := μ)) hp
  rw [integral_sub hiU hiV, Real.norm_eq_abs, integral_const, smul_eq_mul] at h
  exact h.trans (by nlinarith [mul_nonneg L.coe_nonneg hε])

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem mappedTest_box_average (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (δ : ℝ)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    mappedTest μ U (boxTestAverage δ φ) =
      ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * mappedTest μ U (fun x => φ (x + u)) := by
  have hi : Integrable (Function.uncurry
      (fun a u => boxProbabilityWindow (fun _ => δ) 0 u * φ (U a + u))) (μ.prod volume) :=
    ((boxProbabilityWindow_integrable (fun _ => δ) 0).comp_snd μ).mul_bdd
      (hφ.comp ((hU.comp measurable_fst).add measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (U p.1 + p.2)))
  calc
    mappedTest μ U (boxTestAverage δ φ) =
        ∫ a, ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * φ (U a + u) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      exact boxTestAverage_translate δ φ (U a)
    _ = ∫ u, ∫ a, boxProbabilityWindow (fun _ => δ) 0 u * φ (U a + u) ∂μ :=
      integral_integral_swap hi
    _ = ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * mappedTest μ U (fun x => φ (x + u)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integral_const_mul _ _

theorem mappedTest_box_error (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (δ : ℝ) (hδ : 0 < δ) (H : ℝ≥0)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hmove : ∀ z, |mappedTest μ U (fun x => φ (x + z)) - mappedTest μ U φ| ≤ H * dist z 0) :
    |mappedTest μ U (boxTestAverage δ φ) - mappedTest μ U φ| ≤ H * δ := by
  let k := boxProbabilityWindow (fun _ : ι => δ) 0
  let A := fun z => mappedTest μ U (fun x => φ (x + z))
  let I := mappedTest μ U φ
  have hk : Integrable k := boxProbabilityWindow_integrable _ _
  have ha : Integrable (fun u => k u * A u) := hk.mul_bdd
    (mappedTest_shift_measurable μ U hU φ hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => mappedTest_norm_le μ U (fun x => φ (x + z))
      (fun x => hbound (x + z))))
  have hconst : (∫ u, k u * I) = I := by
    rw [integral_mul_const, boxProbabilityWindow_mass _ (fun _ => hδ), one_mul]
  have heq : mappedTest μ U (boxTestAverage δ φ) - I = ∫ u, k u * A u - k u * I := by
    rw [integral_sub ha (hk.mul_const I), hconst]
    rw [mappedTest_box_average μ U hU δ φ hφ hbound]
  have hpoint (u : ι → ℝ) : ‖k u * A u - k u * I‖ ≤ k u * ((H : ℝ) * δ) := by
    by_cases hzero : k u = 0
    · simp only [hzero, zero_mul, sub_self, norm_zero, le_refl]
    · have hdist := boxProbabilityWindow_support_dist δ hδ u hzero
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _),
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((hmove u).trans (mul_le_mul_of_nonneg_left hdist H.coe_nonneg))
        (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _)
  have h := norm_integral_le_of_norm_le (hk.mul_const ((H : ℝ) * δ)) (Filter.Eventually.of_forall hpoint)
  rw [integral_mul_const, boxProbabilityWindow_mass _ (fun _ => hδ), one_mul, Real.norm_eq_abs] at h
  rw [heq]
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxImageComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem box_image_comparison [DecidableEq ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (hmass : μ.real Set.univ ≤ 1) (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (H_U H_V : ℝ≥0) (hTU : ImageTranslationBound μ U H_U) (hTV : ImageTranslationBound μ V H_V)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ᵐ a ∂μ, dist (U a) (V a) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  have hu := mappedTest_box_error μ U hU δ hδ H_U φ hφ hbound (hTU φ hφ hbound)
  have hv := mappedTest_box_error μ V hV δ hδ H_V φ hφ hbound (hTV φ hφ hbound)
  have hLip := boxTestAverage_lipschitz δ hδ φ hφ hbound
  have hmid := coupled_mappedTest_difference μ hmass U V hU hV hε hclose
    (boxTestAverage δ φ) hLip.continuous.measurable (boxTestAverage_norm_le δ hδ φ hbound)
    (boxTestLipschitz (ι := ι) δ hδ) hLip
  have hu' : |mappedTest μ U φ - mappedTest μ U (boxTestAverage δ φ)| ≤ (H_U : ℝ) * δ := by
    rw [abs_sub_comm]
    exact hu
  calc
    |mappedTest μ U φ - mappedTest μ V φ| ≤
        |mappedTest μ U φ - mappedTest μ U (boxTestAverage δ φ)| +
        |mappedTest μ U (boxTestAverage δ φ) - mappedTest μ V φ| := abs_sub_le _ _ _
    _ ≤ |mappedTest μ U φ - mappedTest μ U (boxTestAverage δ φ)| +
        (|mappedTest μ U (boxTestAverage δ φ) - mappedTest μ V (boxTestAverage δ φ)| +
          |mappedTest μ V (boxTestAverage δ φ) - mappedTest μ V φ|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ (H_U : ℝ) * δ + ((boxTestLipschitz (ι := ι) δ hδ : ℝ) * ε + (H_V : ℝ) * δ) :=
      add_le_add hu' (add_le_add hmid hv)
    _ = ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
      rw [boxTestLipschitz_coe]
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CutoffImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : Integrable w μ := by
  apply (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (hbound a).1]
  exact (hbound a).2

theorem cutoffMeasure_mass_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : (realDensityMeasure μ w).real Set.univ ≤ 1 := by
  have hi := cutoff_integrable μ w hw hbound
  rw [realDensityMeasure_real_univ μ w hi (fun a => (hbound a).1)]
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun a => (hbound a).2)
  simpa using h

theorem mappedTest_cutoff_error {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → X) (hU : Measurable U) (φ : X → ℝ) (hφ : Measurable φ)
    (hφbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| ≤ ∫ a, 1 - w a ∂μ := by
  have hwi := cutoff_integrable μ w hw hbound
  have hgi := mappedTest_integrable μ U hU φ hφ hφbound
  have hwgi : Integrable (fun a => w a * φ (U a)) μ :=
    hwi.mul_bdd (hφ.comp hU).aestronglyMeasurable (Filter.Eventually.of_forall (fun a => hφbound _))
  change |(∫ a, φ (U a) ∂μ) - ∫ a, φ (U a) ∂realDensityMeasure μ w| ≤ _
  rw [realDensityMeasure_integral μ w hw (fun a => (hbound a).1), ← integral_sub hgi hwgi]
  have hrem : Integrable (fun a => 1 - w a) μ := (integrable_const (1 : ℝ)).sub hwi
  have hp (a : Ω) : ‖φ (U a) - w a * φ (U a)‖ ≤ 1 - w a := by
    rw [show φ (U a) - w a * φ (U a) = (1 - w a) * φ (U a) by ring, norm_mul,
      Real.norm_of_nonneg (sub_nonneg.mpr (hbound a).2)]
    exact (mul_le_mul_of_nonneg_left (hφbound _) (sub_nonneg.mpr (hbound a).2)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hrem (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CutoffBoxImageComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem cutoff_box_image_comparison (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (H_U H_V : ℝ≥0) (hTU : ImageTranslationBound (realDensityMeasure μ w) U H_U)
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V H_V)
    {ε η : ℝ} (hε : 0 ≤ ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  let : IsFiniteMeasure (realDensityMeasure μ w) :=
    realDensityMeasure_finite μ w (cutoff_integrable μ w hw hw01) (fun a => (hw01 a).1)
  have hsmall := box_image_comparison (realDensityMeasure μ w) (cutoffMeasure_mass_le_one μ w hw hw01)
    U V hU hV H_U H_V hTU hTV hε hclose δ hδ φ hφ hbound
  have hu := (mappedTest_cutoff_error μ w hw hw01 U hU φ hφ hbound).trans hcut
  have hv := (mappedTest_cutoff_error μ w hw hw01 V hV φ hφ hbound).trans hcut
  have hv' : |mappedTest (realDensityMeasure μ w) V φ - mappedTest μ V φ| ≤ η := by
    rw [abs_sub_comm]
    exact hv
  calc
    |mappedTest μ U φ - mappedTest μ V φ| ≤
        |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| +
          |mappedTest (realDensityMeasure μ w) U φ - mappedTest μ V φ| := abs_sub_le _ _ _
    _ ≤ |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| +
        (|mappedTest (realDensityMeasure μ w) U φ - mappedTest (realDensityMeasure μ w) V φ| +
          |mappedTest (realDensityMeasure μ w) V φ - mappedTest μ V φ|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ η + ((((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ) + η) :=
      add_le_add hu (add_le_add hsmall hv')
    _ = 2 * η + ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by ring

theorem sqrt_smoothing_balance {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    b * Real.sqrt (ε / b) + ε / Real.sqrt (ε / b) = 2 * Real.sqrt (b * ε) := by
  let d := Real.sqrt (ε / b)
  have hd : 0 < d := Real.sqrt_pos.mpr (div_pos hε hb)
  have hsq : d ^ 2 = ε / b := Real.sq_sqrt (div_nonneg hε.le hb.le)
  have hbd : b * d ^ 2 = ε := by
    rw [hsq]
    field_simp
  have hdiv : ε / d = b * d := (div_eq_iff hd.ne').mpr (by nlinarith [hbd])
  have hprod : (b * d) ^ 2 = b * ε := by
    calc
      (b * d) ^ 2 = b * (b * d ^ 2) := by ring
      _ = b * ε := by rw [hbd]
  have hroot : b * d = Real.sqrt (b * ε) := by
    nlinarith [Real.sq_sqrt (mul_pos hb hε).le, Real.sqrt_nonneg (b * ε), mul_pos hb hd]
  change b * d + ε / d = _
  rw [hdiv, hroot]
  ring

theorem cutoff_box_image_comparison_sqrt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hTU : ImageTranslationBound (realDensityMeasure μ w) U ((Fintype.card ι : ℝ≥0) * B))
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V ((Fintype.card ι : ℝ≥0) * B))
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have h := cutoff_box_image_comparison μ w hw hw01 U V hU hV _ _ hTU hTV hε.le hcut hclose
    (Real.sqrt (ε / (B : ℝ))) (Real.sqrt_pos.mpr (div_pos hε hB)) φ hφ hbound
  apply h.trans_eq
  have hbal := sqrt_smoothing_balance hB hε
  push_cast
  calc
    2 * η + ((Fintype.card ι : ℝ) * B + (Fintype.card ι : ℝ) * B) * Real.sqrt (ε / (B : ℝ)) +
        2 * (Fintype.card ι : ℝ) * ε / Real.sqrt (ε / (B : ℝ)) =
      2 * η + 2 * (Fintype.card ι : ℝ) *
        ((B : ℝ) * Real.sqrt (ε / (B : ℝ)) + ε / Real.sqrt (ε / (B : ℝ))) := by ring
    _ = 2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by rw [hbal]; ring

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.cutoff_box_image_comparison_sqrt.{u_1, u_2} := @OAI.Erdos3.cutoff_box_image_comparison_sqrt.{u_1, u_2}
