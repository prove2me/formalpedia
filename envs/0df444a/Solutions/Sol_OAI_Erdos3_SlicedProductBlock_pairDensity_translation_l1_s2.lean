-- Prove2me | solution 1 for OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:57.392892+00:00
-- url     : https://prove2.me/submissions/77aa68d9-95d2-4bab-b8ae-ac9c35344efb

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B036
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B060
import Definitions.Def_OAIE3v2B061

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InverseSqrtMoment
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem inverse_max_le_inverse_sqrt_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (max a b)⁻¹ ≤ (Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹ := by
  have hs : 0 < Real.sqrt a * Real.sqrt b := mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)
  rw [← mul_inv]
  apply (inv_le_inv₀ (lt_max_of_lt_left ha) hs).mpr
  have hm : 0 ≤ max a b := (lt_max_of_lt_left ha).le
  have hab : a * b ≤ (max a b) ^ 2 := by
    nlinarith [mul_le_mul (le_max_left a b) (le_max_right a b) hb.le hm]
  have heq : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  nlinarith

theorem unitInverseSqrt_eq_rpow : unitInverseSqrt =
    (Set.Ioc (0 : ℝ) 1).indicator (fun x => x ^ (-1 / 2 : ℝ)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · simp only [unitInverseSqrt, Set.indicator_of_mem hx]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.1.le, ← Real.sqrt_eq_rpow]
  · simp only [unitInverseSqrt, Set.indicator_of_notMem hx]

theorem unitInverseSqrt_integrable : Integrable unitInverseSqrt := by
  rw [unitInverseSqrt_eq_rpow]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -1 / 2)).1

theorem unitInverseSqrt_mass : (∫ x, unitInverseSqrt x) = 2 := by
  rw [unitInverseSqrt_eq_rpow, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num

variable {ι : Type*} [Fintype ι]

theorem unitBoxInverseSqrt_integrable : Integrable (unitBoxInverseSqrt (ι := ι)) :=
  Integrable.fintype_prod (fun _ => unitInverseSqrt_integrable)

theorem unitBoxInverseSqrt_mass : (∫ x : ι → ℝ, unitBoxInverseSqrt x) = 2 ^ Fintype.card ι := by
  unfold unitBoxInverseSqrt
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [unitInverseSqrt_mass, Finset.prod_const, Finset.card_univ]

theorem unitBoxInverseSqrt_eq (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) :
    unitBoxInverseSqrt x = (Real.sqrt (∏ i, x i))⁻¹ := by
  unfold unitBoxInverseSqrt
  simp only [unitInverseSqrt, Set.indicator_of_mem (hx _)]
  rw [Finset.prod_inv_distrib, Real.sqrt_prod _ (fun i _ => (hx i).1.le)]

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

theorem unitBoxMeasure_ae : ∀ᵐ x ∂unitBoxMeasure ι, ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
  filter_upwards [ae_restrict_mem (μ := volume) (positiveUnitBox_measurable (ι := ι))] with x hx
  exact fun i => hx i (Set.mem_univ i)

theorem unitBoxInverseSqrt_indicator : unitBoxInverseSqrt (ι := ι) =
    (positiveUnitBox ι).indicator (fun x => (Real.sqrt (∏ i, x i))⁻¹) := by
  funext x
  by_cases hx : x ∈ positiveUnitBox ι
  · rw [Set.indicator_of_mem hx]
    exact unitBoxInverseSqrt_eq x (fun i => hx i (Set.mem_univ i))
  · rw [Set.indicator_of_notMem hx]
    have h : ¬ ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
      intro hall
      exact hx (fun i _ => hall i)
    push Not at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

theorem unitBox_inverse_sqrt_integrable :
    Integrable (fun x : ι → ℝ => (Real.sqrt (∏ i, x i))⁻¹) (unitBoxMeasure ι) := by
  apply (integrable_indicator_iff positiveUnitBox_measurable).mp
  rw [← unitBoxInverseSqrt_indicator]
  exact unitBoxInverseSqrt_integrable

theorem unitBox_inverse_sqrt_mass :
    (∫ x : ι → ℝ, (Real.sqrt (∏ i, x i))⁻¹ ∂unitBoxMeasure ι) = 2 ^ Fintype.card ι := by
  rw [unitBoxMeasure, ← integral_indicator positiveUnitBox_measurable,
    ← unitBoxInverseSqrt_indicator]
  exact unitBoxInverseSqrt_mass

theorem pairedAmplitude_continuous : Continuous (pairedAmplitude (ι := ι)) := by
  unfold pairedAmplitude
  fun_prop

theorem pairedAmplitude_pos_ae :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι), 0 < pairedAmplitude p := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (unitBoxMeasure_ae (ι := ι))] with p hp
  exact lt_max_of_lt_left (Finset.prod_pos (fun i _ => (hp i).1))

theorem pairedAmplitude_inverse_bound :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι),
      (pairedAmplitude p)⁻¹ ≤ (Real.sqrt (∏ i, p.1 i))⁻¹ * (Real.sqrt (∏ i, p.2 i))⁻¹ := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (unitBoxMeasure_ae (ι := ι)),
    Measure.quasiMeasurePreserving_snd.ae (unitBoxMeasure_ae (ι := ι))] with p hp hq
  exact inverse_max_le_inverse_sqrt_product (Finset.prod_pos (fun i _ => (hp i).1))
    (Finset.prod_pos (fun i _ => (hq i).1))

theorem pairedAmplitude_inverse_integrable :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) => (pairedAmplitude p)⁻¹)
      ((unitBoxMeasure ι).prod (unitBoxMeasure ι)) := by
  have hi := (unitBox_inverse_sqrt_integrable (ι := ι)).mul_prod
    (unitBox_inverse_sqrt_integrable (ι := ι))
  apply hi.mono' pairedAmplitude_continuous.measurable.inv.aestronglyMeasurable
  filter_upwards [pairedAmplitude_inverse_bound (ι := ι), pairedAmplitude_pos_ae (ι := ι)] with p hp hpos
  change ‖(pairedAmplitude p)⁻¹‖ ≤ _
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact hp

theorem pairedAmplitude_inverse_integral_le :
    (∫ p : (ι → ℝ) × (ι → ℝ), (pairedAmplitude p)⁻¹
      ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι)) ≤ 4 ^ Fintype.card ι := by
  have hi := (unitBox_inverse_sqrt_integrable (ι := ι)).mul_prod
    (unitBox_inverse_sqrt_integrable (ι := ι))
  have h := integral_mono_ae (pairedAmplitude_inverse_integrable (ι := ι)) hi
    (pairedAmplitude_inverse_bound (ι := ι))
  rw [integral_prod_mul (fun x : ι → ℝ => (Real.sqrt (∏ i, x i))⁻¹)
    (fun x : ι → ℝ => (Real.sqrt (∏ i, x i))⁻¹), unitBox_inverse_sqrt_mass, ← mul_pow] at h
  norm_num only [show (2 : ℝ) * 2 = 4 by norm_num] at h
  exact h

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

theorem densityMixture_l1_le {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite μ] [SFinite ν]
    (F G : T → X → ℝ)
    (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (hG : Integrable (Function.uncurry G) (μ.prod ν)) :
    (∫ x, ‖densityMixture μ F x - densityMixture μ G x‖ ∂ν) ≤
      ∫ t, ∫ x, ‖F t x - G t x‖ ∂ν ∂μ := by
  have hd : Integrable (Function.uncurry (fun t x => F t x - G t x)) (μ.prod ν) := hF.sub hG
  have hm : Integrable (fun x => densityMixture μ F x - densityMixture μ G x) ν :=
    hF.integral_prod_right.sub hG.integral_prod_right
  calc
    (∫ x, ‖densityMixture μ F x - densityMixture μ G x‖ ∂ν) ≤
        ∫ x, ∫ t, ‖F t x - G t x‖ ∂μ ∂ν := by
      apply integral_mono_ae hm.norm hd.integral_norm_prod_right
      filter_upwards [hF.prod_left_ae, hG.prod_left_ae] with x hfx hgx
      change Integrable (fun t => F t x) μ at hfx
      change Integrable (fun t => G t x) μ at hgx
      change ‖(∫ t, F t x ∂μ) - ∫ t, G t x ∂μ‖ ≤ _
      rw [← integral_sub hfx hgx]
      exact norm_integral_le_integral_norm _
    _ = ∫ t, ∫ x, ‖F t x - G t x‖ ∂ν ∂μ := (integral_integral_swap hd.norm).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem measurable_normalizedIntervalWindow {T : Type*} [MeasurableSpace T]
    (ℓ s t : T → ℝ) (hℓ : Measurable ℓ) (hs : Measurable s) (ht : Measurable t) :
    Measurable (fun u => normalizedIntervalWindow (ℓ u) (s u) (t u)) := by
  have hm : MeasurableSet {u | s u < t u ∧ t u ≤ s u + ℓ u} :=
    (measurableSet_lt hs ht).inter (measurableSet_le ht (hs.add hℓ))
  have hn : Measurable ({u | s u < t u ∧ t u ≤ s u + ℓ u}.indicator (fun _ : T => (1 : ℝ))) :=
    measurable_const.indicator hm
  exact hn.div hℓ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourProductSmoothing
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem normalizedIntervalWindow_add_arg (ℓ s x a : ℝ) :
    normalizedIntervalWindow ℓ s (x + a) = normalizedIntervalWindow ℓ (s - a) x := by
  calc
    normalizedIntervalWindow ℓ s (x + a) = normalizedIntervalWindow ℓ 0 (x + a - s) :=
      normalizedIntervalWindow_translate _ _ _
    _ = normalizedIntervalWindow ℓ 0 (x - (s - a)) := by congr 1; ring
    _ = normalizedIntervalWindow ℓ (s - a) x := (normalizedIntervalWindow_translate _ _ _).symm

theorem randomIntervalDensity_add_arg {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) (x a : ℝ) :
    randomIntervalDensity μ ℓ s (x + a) =
      randomIntervalDensity μ ℓ (fun t => s t - a) x := by
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalizedIntervalWindow_add_arg _ _ _ _

theorem randomIntervalDensity_translation_l1 {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (ℓ s : T → ℝ)
    (hℓ : Measurable ℓ) (hs : Measurable s) (hpos : ∀ᵐ t ∂μ, 0 < ℓ t)
    (hi : Integrable (fun t => (ℓ t)⁻¹) μ) (a b : ℝ) :
    (∫ x, |randomIntervalDensity μ ℓ s (x + a) - randomIntervalDensity μ ℓ s (x + b)|) ≤
      2 * (∫ t, (ℓ t)⁻¹ ∂μ) * |a - b| := by
  have hj (c : ℝ) : Integrable (Function.uncurry
      (fun t x => normalizedIntervalWindow (ℓ t) (s t - c) x)) (μ.prod volume) := by
    apply densityMixture_joint_integrable μ volume _
    · exact measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
        ((hs.sub_const c).comp measurable_fst) measurable_snd
    · filter_upwards [hpos] with t ht
      exact ⟨normalizedIntervalWindow_nonneg ht _, normalizedIntervalWindow_integrable _ _,
        normalizedIntervalWindow_mass ht _⟩
  have hd : Integrable (Function.uncurry (fun t x =>
      normalizedIntervalWindow (ℓ t) (s t - a) x -
      normalizedIntervalWindow (ℓ t) (s t - b) x)) (μ.prod volume) := (hj a).sub (hj b)
  have h := densityMixture_l1_le μ volume _ _ (hj a) (hj b)
  simp only [Real.norm_eq_abs] at h
  simp_rw [randomIntervalDensity_add_arg]
  apply h.trans
  have hb : ∀ᵐ t ∂μ, (∫ x, |normalizedIntervalWindow (ℓ t) (s t - a) x -
      normalizedIntervalWindow (ℓ t) (s t - b) x|) ≤ 2 * (ℓ t)⁻¹ * |a - b| := by
    filter_upwards [hpos] with t ht
    have hbound := normalizedIntervalWindow_translation_le ht (s t - a) (s t - b)
    rwa [show s t - a - (s t - b) = -(a - b) by ring, abs_neg, div_eq_mul_inv] at hbound
  have hmono := integral_mono_ae hd.integral_norm_prod_left
    ((hi.const_mul 2).mul_const |a - b|) (by
      filter_upwards [hb] with t ht
      exact ht)
  rw [integral_mul_const, integral_const_mul] at hmono
  exact hmono

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPairAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace SlicedProductBlock

variable {ι : Type*} [Fintype ι]

theorem prefixProduct_continuous (B : SlicedProductBlock ι) : Continuous B.prefixProduct := by
  unfold prefixProduct
  fun_prop

theorem slope_continuous (B : SlicedProductBlock ι) : Continuous B.slope :=
  continuous_const.mul B.prefixProduct_continuous

theorem base_continuous (B : SlicedProductBlock ι) : Continuous B.base :=
  continuous_const.mul B.prefixProduct_continuous

theorem prefixProduct_nonneg {B : SlicedProductBlock ι} (hB : B.Admissible)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ B.prefixProduct x :=
  Finset.prod_nonneg (fun i _ => add_nonneg (hB.lower_nonneg i)
    (mul_nonneg (hB.width_pos i).le (hx i).1.le))

theorem slope_lower {B : SlicedProductBlock ι} (hB : B.Admissible)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) :
    B.volumeScale * (∏ i, x i) ≤ |B.slope x| := by
  have hp : (∏ i, B.width i) * (∏ i, x i) ≤ B.prefixProduct x := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod
      (fun i _ => mul_nonneg (hB.width_pos i).le (hx i).1.le)
      (fun i _ => le_add_of_nonneg_left (hB.lower_nonneg i))
  have h := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (abs_nonneg B.coefficient) hB.lastWidth_pos.le)
  simpa only [volumeScale, slope, abs_mul, abs_of_pos hB.lastWidth_pos,
    abs_of_nonneg (prefixProduct_nonneg hB hx), mul_assoc] using h

end SlicedProductBlock

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem pairWidth_measurable (A B : SlicedProductBlock ι) : Measurable (pairWidth A B) :=
  ((A.slope_continuous.measurable.comp measurable_fst).abs).max
    (B.slope_continuous.measurable.comp measurable_snd).abs

theorem pairWidth_lower {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι),
      pairScale A B * pairedAmplitude p ≤ pairWidth A B p := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (unitBoxMeasure_ae (ι := ι)),
    Measure.quasiMeasurePreserving_snd.ae (unitBoxMeasure_ae (ι := ι))] with p hp hq
  have hleft : pairScale A B * (∏ i, p.1 i) ≤ |A.slope p.1| :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Finset.prod_nonneg (fun i _ => (hp i).1.le))).trans
      (slope_lower hA hp)
  have hright : pairScale A B * (∏ i, p.2 i) ≤ |B.slope p.2| :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Finset.prod_nonneg (fun i _ => (hq i).1.le))).trans
      (slope_lower hB hq)
  change pairScale A B * max (∏ i, p.1 i) (∏ i, p.2 i) ≤ _
  rw [mul_max_of_nonneg _ _ (pairScale_pos hA hB).le]
  exact max_le_max hleft hright

theorem pairWidth_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι), 0 < pairWidth A B p := by
  filter_upwards [pairWidth_lower hA hB, pairedAmplitude_pos_ae (ι := ι)] with p hp hpos
  exact (mul_pos (pairScale_pos hA hB) hpos).trans_le hp

theorem pairWidth_inverse_bound {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι),
      (pairWidth A B p)⁻¹ ≤ (pairScale A B)⁻¹ * (pairedAmplitude p)⁻¹ := by
  filter_upwards [pairWidth_lower hA hB, pairedAmplitude_pos_ae (ι := ι)] with p hp hpos
  have hlow := mul_pos (pairScale_pos hA hB) hpos
  rw [← mul_inv]
  exact (inv_le_inv₀ (hlow.trans_le hp) hlow).mpr hp

theorem pairWidth_inverse_integrable {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    Integrable (fun p => (pairWidth A B p)⁻¹) ((unitBoxMeasure ι).prod (unitBoxMeasure ι)) := by
  apply (pairedAmplitude_inverse_integrable.const_mul (pairScale A B)⁻¹).mono'
    (pairWidth_measurable A B).inv.aestronglyMeasurable
  filter_upwards [pairWidth_inverse_bound hA hB, pairWidth_pos hA hB] with p hp hpos
  change ‖(pairWidth A B p)⁻¹‖ ≤ _
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact hp

theorem pairWidth_inverse_integral_le {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    (∫ p, (pairWidth A B p)⁻¹ ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι)) ≤ pairCap A B := by
  have h := integral_mono_ae (pairWidth_inverse_integrable hA hB)
    (pairedAmplitude_inverse_integrable.const_mul (pairScale A B)⁻¹) (pairWidth_inverse_bound hA hB)
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left pairedAmplitude_inverse_integral_le
    (inv_nonneg.mpr (pairScale_pos hA hB).le))

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RandomAffinePair
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T : Type*} [MeasurableSpace T]

theorem affinePairWidth_measurable {a b : T → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (affinePairWidth a b) := (ha.abs.max hb.abs).comp measurable_fst

theorem affinePairShift_measurable {a b c : T → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (affinePairShift a b c) := by
  unfold affinePairShift
  fun_prop

theorem affinePairWidth_inverse_integral (μ : Measure T) [SFinite μ] (a b : T → ℝ) :
    (∫ p, (affinePairWidth a b p)⁻¹ ∂μ.prod unitScalarMeasure) =
      ∫ t, (max |a t| |b t|)⁻¹ ∂μ := by
  unfold affinePairWidth
  rw [integral_fun_fst (fun t => (max |a t| |b t|)⁻¹), probReal_univ, one_smul]

theorem affinePairDensity_translation_l1 (μ : Measure T) [IsProbabilityMeasure μ]
    {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|)
    (hi : Integrable (fun t => (max |a t| |b t|)⁻¹) μ) (x y : ℝ) :
    (∫ u, |affinePairDensity μ a b c (u + x) - affinePairDensity μ a b c (u + y)|) ≤
      2 * (∫ t, (max |a t| |b t|)⁻¹ ∂μ) * |x - y| := by
  have h := randomIntervalDensity_translation_l1 (μ.prod unitScalarMeasure) _ _
    (affinePairWidth_measurable ha hb) (affinePairShift_measurable ha hb hc)
    (Measure.quasiMeasurePreserving_fst.ae hpos) (hi.comp_fst unitScalarMeasure) x y
  rw [affinePairWidth_inverse_integral] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedPairDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem pairDensity_translation_l1_s2_oai {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (x y : ℝ) :
    (∫ u, |pairDensity A B (u + x) - pairDensity A B (u + y)|) ≤
      2 * pairCap A B * |x - y| := by
  have h := affinePairDensity_translation_l1 ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd))
    (pairWidth_pos hA hB) (pairWidth_inverse_integrable hA hB) x y
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pairWidth_inverse_integral_le hA hB) (by norm_num)) (abs_nonneg _))

end Erdos3.SlicedProductBlock

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1_s2_oai.{u_1} := @OAI.Erdos3.SlicedProductBlock.pairDensity_translation_l1_s2_oai.{u_1}
