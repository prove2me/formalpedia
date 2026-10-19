-- Prove2me | solution 1 for OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:58.805105+00:00
-- url     : https://prove2.me/submissions/e1423374-a51b-4fc6-acf8-39c3ab810027

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B032
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B036
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B080
import Theorems.Thm_OAI_Erdos3_SlicedProductBlock_pairDensity_translation_l1_s2

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

theorem normalizedIntervalWindow_mass {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    (∫ t, normalizedIntervalWindow ℓ x t) = 1 := by
  unfold normalizedIntervalWindow
  rw [integral_div, integral_intervalWindow]
  simp only [add_sub_cancel_left, max_eq_left hℓ.le, div_self hℓ.ne']

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

theorem fixedKernelMixture_lipschitz {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (K : T → ℝ) (g : X → T → ℝ) (L : ℝ≥0)
    (hK : Integrable K μ) (hK0 : ∀ t, 0 ≤ K t) (hKmass : (∫ t, K t ∂μ) = 1)
    (hint : ∀ x, Integrable (fun t => K t * g x t) μ)
    (hLip : ∀ t, LipschitzWith L (fun x => g x t)) :
    LipschitzWith L (fun x => ∫ t, K t * g x t ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← integral_sub (hint x) (hint y)]
  have hpoint (t) : ‖K t * g x t - K t * g y t‖ ≤ K t * ((L : ℝ) * dist x y) := by
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hK0 t)]
    apply mul_le_mul_of_nonneg_left _ (hK0 t)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using (hLip t).dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hK.mul_const ((L : ℝ) * dist x y))
    (Filter.Eventually.of_forall hpoint)
  simpa only [Real.norm_eq_abs, integral_mul_const, hKmass, one_mul] using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPairAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace SlicedProductBlock

variable {ι : Type*} [Fintype ι]

theorem value_eq (B : SlicedProductBlock ι) (x : ι → ℝ) (u : ℝ) :
    B.value x u = B.base x + B.slope x * u := by
  unfold value base slope
  ring

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

theorem volumeScale_lower {B : SlicedProductBlock ι} {c δ : ℝ} (_hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hcoeff : c ≤ |B.coefficient|) (hlast : δ ≤ B.lastWidth) (hwidth : ∀ i, δ ≤ B.width i) :
    c * δ ^ (Fintype.card ι + 1) ≤ B.volumeScale := by
  have hp : δ ^ Fintype.card ι ≤ ∏ i, B.width i := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun _ _ => hδ) (fun i _ => hwidth i)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  have h := mul_le_mul (mul_le_mul hcoeff hlast hδ (abs_nonneg _)) hp
    (pow_nonneg hδ _) (mul_nonneg (abs_nonneg _) (hδ.trans hlast))
  simpa only [volumeScale, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

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

theorem pairCap_le_of_scale_lower {A B : SlicedProductBlock ι} {r : ℝ}
    (hr : 0 < r) (hA : r ≤ A.volumeScale) (hB : r ≤ B.volumeScale) :
    pairCap A B ≤ r⁻¹ * 4 ^ Fintype.card ι := by
  have hscale : r ≤ pairScale A B := le_min hA hB
  exact mul_le_mul_of_nonneg_right
    ((inv_le_inv₀ (hr.trans_le hscale) hr).mpr hscale) (by positivity)

end Erdos3.SlicedProductBlock

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

theorem randomIntervalDensity_cap {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) (hℓ : Measurable ℓ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ, 0 < ℓ t) (hi : Integrable (fun t => (ℓ t)⁻¹) μ) (x : ℝ) :
    randomIntervalDensity μ ℓ s x ∈ Set.Icc (0 : ℝ) (∫ t, (ℓ t)⁻¹ ∂μ) := by
  apply densityMixture_cap μ _ _ hi
  · intro y
    exact (measurable_normalizedIntervalWindow ℓ s (fun _ => y) hℓ hs measurable_const).aestronglyMeasurable
  · filter_upwards [hpos] with t ht
    intro y
    exact ⟨normalizedIntervalWindow_nonneg ht _ _, by simpa only [one_div] using normalizedIntervalWindow_le ht (s t) y⟩

theorem randomIntervalDensity_probability_density {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (ℓ s : T → ℝ)
    (hℓ : Measurable ℓ) (hs : Measurable s) (hpos : ∀ᵐ t ∂μ, 0 < ℓ t) :
    (∀ x, 0 ≤ randomIntervalDensity μ ℓ s x) ∧ Integrable (randomIntervalDensity μ ℓ s) ∧
      (∫ x, randomIntervalDensity μ ℓ s x) = 1 := by
  apply densityMixture_probability_density μ volume _
  · exact measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
      (hs.comp measurable_fst) measurable_snd
  · filter_upwards [hpos] with t ht
    exact ⟨normalizedIntervalWindow_nonneg ht _, normalizedIntervalWindow_integrable _ _,
      normalizedIntervalWindow_mass ht _⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem normalizedIntervalWindow_test_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) (φ : ℝ → ℝ) :
    (∫ x, normalizedIntervalWindow ℓ s x * φ x) =
      ∫ u, φ (s + ℓ * u) ∂unitScalarMeasure := by
  have heq (x : ℝ) : normalizedIntervalWindow ℓ s x * φ x =
      (Set.Ioc s (s + ℓ)).indicator φ x / ℓ := by
    by_cases hx : x ∈ Set.Ioc s (s + ℓ)
    · simp only [normalizedIntervalWindow, intervalWindow, Set.indicator_of_mem hx]
      ring
    · simp only [normalizedIntervalWindow, intervalWindow, Set.indicator_of_notMem hx, zero_div, zero_mul]
  simp_rw [heq]
  rw [integral_div, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : s ≤ s + ℓ)]
  change _ = ∫ u in Set.Ioc (0 : ℝ) 1, φ (s + ℓ * u)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_add_mul φ hℓ.ne' s]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem randomIntervalDensity_measurable {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [SFinite μ] (ℓ s : T → ℝ) (hℓ : Measurable ℓ) (hs : Measurable s) :
    Measurable (randomIntervalDensity μ ℓ s) := by
  have hm : Measurable (fun p : T × ℝ => normalizedIntervalWindow (ℓ p.1) (s p.1) p.2) :=
    measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
      (hs.comp measurable_fst) measurable_snd
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

theorem randomIntervalDensity_test_integral {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (ℓ s : T → ℝ)
    (hℓ : Measurable ℓ) (hs : Measurable s) (hpos : ∀ᵐ t ∂μ, 0 < ℓ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, randomIntervalDensity μ ℓ s x * φ x) =
      ∫ t, ∫ u, φ (s t + ℓ t * u) ∂unitScalarMeasure ∂μ := by
  have hm : Measurable (fun p : T × ℝ => normalizedIntervalWindow (ℓ p.1) (s p.1) p.2) :=
    measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
      (hs.comp measurable_fst) measurable_snd
  have hd : ∀ᵐ t ∂μ, (∀ x, 0 ≤ normalizedIntervalWindow (ℓ t) (s t) x) ∧
      Integrable (normalizedIntervalWindow (ℓ t) (s t)) ∧
      (∫ x, normalizedIntervalWindow (ℓ t) (s t) x) = 1 := by
    filter_upwards [hpos] with t ht
    exact ⟨normalizedIntervalWindow_nonneg ht _, normalizedIntervalWindow_integrable _ _,
      normalizedIntervalWindow_mass ht _⟩
  have hi : Integrable (Function.uncurry
      (fun t x => normalizedIntervalWindow (ℓ t) (s t) x * φ x)) (μ.prod volume) :=
    (densityMixture_joint_integrable μ volume _ hm hd).mul_bdd
      (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.2))
  calc
    (∫ x, randomIntervalDensity μ ℓ s x * φ x) =
        ∫ x, ∫ t, normalizedIntervalWindow (ℓ t) (s t) x * φ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, normalizedIntervalWindow (ℓ t) (s t) x * φ x ∂volume ∂μ :=
      (integral_integral_swap hi).symm
    _ = ∫ t, ∫ u, φ (s t + ℓ t * u) ∂unitScalarMeasure ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpos] with t ht
      exact normalizedIntervalWindow_test_integral ht _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T : Type*} [MeasurableSpace T]

theorem independentShiftDensity_cap (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f)
    {C : ℝ} (hcap : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (x : ℝ) :
    independentShiftDensity μ z f x ∈ Set.Icc (0 : ℝ) C := by
  have h := densityMixture_cap μ (fun t x => f (x - z t)) (fun _ => C) (integrable_const C)
    (fun x => (hf.comp (measurable_const.sub hz)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t x => hcap (x - z t))) x
  simp only [integral_const, probReal_univ, one_smul] at h
  exact h

theorem independentShiftDensity_lipschitz (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (L : ℝ≥0) (hf : LipschitzWith L f)
    {C : ℝ} (hcap : ∀ x, ‖f x‖ ≤ C) :
    LipschitzWith L (independentShiftDensity μ z f) := by
  have hi (x : ℝ) : Integrable (fun t => f (x - z t)) μ :=
    (integrable_const C).mono'
      (hf.continuous.measurable.comp (measurable_const.sub hz)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => hcap (x - z t)))
  have h := fixedKernelMixture_lipschitz μ (fun _ => (1 : ℝ)) (fun x t => f (x - z t)) L
    (integrable_const 1) (fun _ => zero_le_one) (by simp)
    (fun x => by simpa only [one_mul] using hi x) (fun t => by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_sub_right] using hf.dist_le_mul (x - z t) (y - z t))
  simp only [one_mul] at h
  exact h

theorem independentShiftDensity_probability_density (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x) = 1) :
    (∀ x, 0 ≤ independentShiftDensity μ z f x) ∧ Integrable (independentShiftDensity μ z f) ∧
      (∫ x, independentShiftDensity μ z f x) = 1 := by
  apply densityMixture_probability_density μ volume _
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · filter_upwards [] with t
    exact ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarDensityConvolution_lipschitz (f g : ℝ → ℝ) (C D : ℝ≥0)
    (hf : Integrable f) (hg : Measurable g) (hcap : ∀ t, ‖g t‖ ≤ C)
    (hmove : ∀ a b, (∫ u, |f (u + a) - f (u + b)|) ≤ D * |a - b|) :
    LipschitzWith (C * D) (scalarDensityConvolution f g) := by
  apply kernelAverage_lipschitz volume (fun x t => f (x - t)) g C D
    (fun x => hf.comp_sub_left x) hg.aestronglyMeasurable hcap
  intro x y
  rw [← integral_neg_eq_self (fun t => |f (x - t) - f (y - t)|) volume]
  simpa only [sub_neg_eq_add, add_comm, Real.dist_eq] using hmove x y

theorem scalarDensityConvolution_cap (f g : ℝ → ℝ) (hf : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hfmass : (∫ t, f t) = 1) (hg : Measurable g)
    {C : ℝ} (hcap : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ℝ) :
    scalarDensityConvolution f g x ∈ Set.Icc (0 : ℝ) C := by
  refine ⟨integral_nonneg (fun t => mul_nonneg (hf0 _) (hcap t).1), ?_⟩
  apply kernelAverage_cap volume (fun x t => f (x - t)) g (fun x => hf.comp_sub_left x)
    (fun x t => hf0 (x - t)) _ hg.aestronglyMeasurable hcap x
  intro y
  rw [integral_sub_left_eq_self f volume y, hfmass]

theorem scalarDensityConvolution_joint_integrable (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2) (volume.prod volume) := by
  have hm := (hfm.comp (measurable_fst.sub measurable_snd)).mul (hgm.comp measurable_snd)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun t => (hf.comp_sub_right t).mul_const (g t)), ?_⟩
  have heq (t : ℝ) : (∫ x, ‖f (x - t) * g t‖) = (∫ x, ‖f x‖) * ‖g t‖ := by
    simp only [norm_mul, integral_mul_const]
    rw [integral_sub_right_eq_self (fun x => ‖f x‖) t]
  change Integrable (fun t => ∫ x, ‖f (x - t) * g t‖)
  simp_rw [heq]
  exact hg.norm.const_mul _

theorem scalarDensityConvolution_integrable (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g) :
    Integrable (scalarDensityConvolution f g) :=
  (scalarDensityConvolution_joint_integrable f g hfm hgm hf hg).integral_prod_left

theorem scalarDensityConvolution_mass (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, scalarDensityConvolution f g x) = (∫ x, f x) * ∫ x, g x := by
  have hi : Integrable (Function.uncurry (fun x t => f (x - t) * g t)) (volume.prod volume) :=
    scalarDensityConvolution_joint_integrable f g hfm hgm hf hg
  unfold scalarDensityConvolution
  rw [integral_integral_swap hi]
  simp_rw [integral_mul_const, integral_sub_right_eq_self f]
  exact integral_const_mul _ _

theorem scalarDensityConvolution_test_integral (f g φ : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, scalarDensityConvolution f g x * φ x) =
      ∫ t, g t * ∫ u, f u * φ (u + t) := by
  have hi : Integrable (Function.uncurry (fun x t => (f (x - t) * g t) * φ x))
      (volume.prod volume) :=
    (scalarDensityConvolution_joint_integrable f g hfm hgm hf hg).mul_bdd
      (hφ.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.1))
  calc
    (∫ x, scalarDensityConvolution f g x * φ x) =
        ∫ x, ∫ t, (f (x - t) * g t) * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, (f (x - t) * g t) * φ x := integral_integral_swap hi
    _ = ∫ t, g t * ∫ u, f u * φ (u + t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have h := integral_add_right_eq_self (μ := volume) (fun x => (f (x - t) * g t) * φ x) t
      simp only [add_sub_cancel_right] at h
      rw [← h]
      simp only [mul_comm (f _), mul_assoc, integral_const_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem imageLaw_eq_density_of_bounded_tests
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X)
    (U : Ω → X) (hU : Measurable U)
    (f : X → ℝ) (hf : Measurable f) (hfi : Integrable f ν) (hf0 : ∀ x, 0 ≤ f x)
    (htest : ∀ φ : X → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      (∫ a, φ (U a) ∂μ) = ∫ x, f x * φ x ∂ν) :
    μ.map U = realDensityMeasure ν f := by
  let : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  let : IsFiniteMeasure (realDensityMeasure ν f) := realDensityMeasure_finite ν f hfi hf0
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := htest (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  rw [← integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable,
    ← realDensityMeasure_integral ν f hf hf0] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

theorem scalarDensityConvolution_image_law (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmass : (∫ x, f x) = 1) (hgmass : (∫ x, g x) = 1) :
    ((realDensityMeasure volume g).prod (realDensityMeasure volume f)).map
      (fun p : ℝ × ℝ => p.2 + p.1) =
        realDensityMeasure volume (scalarDensityConvolution f g) := by
  let : IsProbabilityMeasure (realDensityMeasure volume f) :=
    realDensityMeasure_probability volume f hf hf0 hfmass
  let : IsProbabilityMeasure (realDensityMeasure volume g) :=
    realDensityMeasure_probability volume g hg hg0 hgmass
  have hm : Measurable (scalarDensityConvolution f g) :=
    ((hfm.comp (measurable_fst.sub measurable_snd)).mul
      (hgm.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  apply imageLaw_eq_density_of_bounded_tests _ volume _ (measurable_snd.add measurable_fst)
    _ hm (scalarDensityConvolution_integrable f g hfm hgm hf hg)
    (fun x => integral_nonneg (fun t => mul_nonneg (hf0 _) (hg0 _)))
  intro φ hφ hb
  have hi : Integrable (fun p : ℝ × ℝ => φ (p.2 + p.1))
      ((realDensityMeasure volume g).prod (realDensityMeasure volume f)) :=
    (integrable_const (1 : ℝ)).mono'
      (hφ.comp (measurable_snd.add measurable_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hb _))
  change (∫ p : ℝ × ℝ, φ (p.2 + p.1)
    ∂(realDensityMeasure volume g).prod (realDensityMeasure volume f)) = _
  rw [integral_prod _ hi]
  simp_rw [realDensityMeasure_integral volume f hfm hf0]
  rw [realDensityMeasure_integral volume g hgm hg0]
  exact (scalarDensityConvolution_test_integral f g φ hfm hgm hf hg hφ hb).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem uniform_two_term_sum_sort (a b : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ u, ∫ v, φ (min a b * u + max a b * v) ∂unitScalarMeasure ∂unitScalarMeasure) =
      ∫ u, ∫ v, φ (a * u + b * v) ∂unitScalarMeasure ∂unitScalarMeasure := by
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab]
    have hi : Integrable (Function.uncurry (fun u v => φ (b * u + a * v)))
        (unitScalarMeasure.prod unitScalarMeasure) := by
      apply (integrable_const C).mono'
      · exact (hφ.comp ((measurable_const.mul measurable_fst).add
          (measurable_const.mul measurable_snd))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun p => hbound (b * p.1 + a * p.2))
    have h := integral_integral_swap hi
    conv_rhs at h => arg 2; ext u; arg 2; ext v; rw [add_comm]
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RandomAffinePair
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem unitScalarMeasure_reflection (f : ℝ → ℝ) :
    (∫ u, f (1 - u) ∂unitScalarMeasure) = ∫ u, f u ∂unitScalarMeasure := by
  change (∫ u in Set.Ioc (0 : ℝ) 1, f (1 - u)) = ∫ u in Set.Ioc (0 : ℝ) 1, f u
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left f 1]
  norm_num

theorem uniform_signed_slope_normalize (a : ℝ) (f : ℝ → ℝ) :
    (∫ u, f (a * u) ∂unitScalarMeasure) =
      ∫ u, f (min 0 a + |a| * u) ∂unitScalarMeasure := by
  by_cases ha : 0 ≤ a
  · simp only [min_eq_left ha, abs_of_nonneg ha, zero_add]
  · have ha' : a < 0 := lt_of_not_ge ha
    calc
      (∫ u, f (a * u) ∂unitScalarMeasure) =
          ∫ u, f (a * (1 - u)) ∂unitScalarMeasure := (unitScalarMeasure_reflection _).symm
      _ = ∫ u, f (min 0 a + |a| * u) ∂unitScalarMeasure := by
        apply integral_congr_ae
        filter_upwards [] with u
        congr 1
        rw [min_eq_right ha'.le, abs_of_neg ha']
        ring

theorem uniform_two_affine_normalize (a b c : ℝ) (φ : ℝ → ℝ) :
    (∫ u, ∫ v, φ (c + a * u + b * v) ∂unitScalarMeasure ∂unitScalarMeasure) =
      ∫ u, ∫ v, φ (c + min 0 a + min 0 b + (|a| * u + |b| * v))
        ∂unitScalarMeasure ∂unitScalarMeasure := by
  have ha := uniform_signed_slope_normalize a
    (fun x => ∫ v, φ (c + x + b * v) ∂unitScalarMeasure)
  apply ha.trans
  apply integral_congr_ae
  filter_upwards [] with u
  have hb := uniform_signed_slope_normalize b (fun y => φ (c + (min 0 a + |a| * u) + y))
  apply hb.trans
  apply integral_congr_ae
  filter_upwards [] with v
  congr 1
  ring

theorem uniform_two_affine_sort (a b c : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ u, ∫ v, φ (c + min 0 a + min 0 b + min |a| |b| * u + max |a| |b| * v)
      ∂unitScalarMeasure ∂unitScalarMeasure) =
      ∫ u, ∫ v, φ (c + a * u + b * v) ∂unitScalarMeasure ∂unitScalarMeasure := by
  have h := uniform_two_term_sum_sort |a| |b|
    (fun z => φ (c + min 0 a + min 0 b + z))
    (hφ.comp (measurable_const.add measurable_id)) (fun z => hbound _)
  have hn := uniform_two_affine_normalize a b c φ
  simpa only [add_assoc] using h.trans hn.symm

end Erdos3

end

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

theorem affinePairDensity_measurable (μ : Measure T) [SFinite μ] {a b c : T → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (affinePairDensity μ a b c) :=
  randomIntervalDensity_measurable _ _ _ (affinePairWidth_measurable ha hb)
    (affinePairShift_measurable ha hb hc)

theorem affinePairWidth_inverse_integral (μ : Measure T) [SFinite μ] (a b : T → ℝ) :
    (∫ p, (affinePairWidth a b p)⁻¹ ∂μ.prod unitScalarMeasure) =
      ∫ t, (max |a t| |b t|)⁻¹ ∂μ := by
  unfold affinePairWidth
  rw [integral_fun_fst (fun t => (max |a t| |b t|)⁻¹), probReal_univ, one_smul]

theorem affinePairDensity_cap (μ : Measure T) [IsProbabilityMeasure μ] {a b c : T → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|)
    (hi : Integrable (fun t => (max |a t| |b t|)⁻¹) μ) (x : ℝ) :
    affinePairDensity μ a b c x ∈ Set.Icc (0 : ℝ) (∫ t, (max |a t| |b t|)⁻¹ ∂μ) := by
  have h := randomIntervalDensity_cap (μ.prod unitScalarMeasure) _ _
    (affinePairWidth_measurable ha hb) (affinePairShift_measurable ha hb hc)
    (Measure.quasiMeasurePreserving_fst.ae hpos) (hi.comp_fst unitScalarMeasure) x
  rw [affinePairWidth_inverse_integral] at h
  exact h

theorem affinePairDensity_probability_density (μ : Measure T) [IsProbabilityMeasure μ]
    {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|) :
    (∀ x, 0 ≤ affinePairDensity μ a b c x) ∧ Integrable (affinePairDensity μ a b c) ∧
      (∫ x, affinePairDensity μ a b c x) = 1 :=
  randomIntervalDensity_probability_density _ _ _ (affinePairWidth_measurable ha hb)
    (affinePairShift_measurable ha hb hc) (Measure.quasiMeasurePreserving_fst.ae hpos)

theorem affinePairDensity_test_integral (μ : Measure T) [IsProbabilityMeasure μ]
    {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, affinePairDensity μ a b c x * φ x) =
      ∫ t, ∫ u, ∫ v, φ (c t + a t * u + b t * v)
        ∂unitScalarMeasure ∂unitScalarMeasure ∂μ := by
  have h := randomIntervalDensity_test_integral (μ.prod unitScalarMeasure) _ _
    (affinePairWidth_measurable ha hb) (affinePairShift_measurable ha hb hc)
    (Measure.quasiMeasurePreserving_fst.ae hpos) φ hφ hbound
  apply h.trans
  have hm : Measurable (fun p : (T × ℝ) × ℝ =>
      φ (affinePairShift a b c p.1 + affinePairWidth a b p.1 * p.2)) :=
    hφ.comp (((affinePairShift_measurable ha hb hc).comp measurable_fst).add
      (((affinePairWidth_measurable ha hb).comp measurable_fst).mul measurable_snd))
  have hi : Integrable (fun p : (T × ℝ) × ℝ =>
      φ (affinePairShift a b c p.1 + affinePairWidth a b p.1 * p.2))
      ((μ.prod unitScalarMeasure).prod unitScalarMeasure) :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound _))
  rw [integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with t
  exact uniform_two_affine_sort (a t) (b t) (c t) φ hφ hbound

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

theorem pairDensity_measurable (A B : SlicedProductBlock ι) : Measurable (pairDensity A B) :=
  affinePairDensity_measurable _ (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd))

theorem pairDensity_cap {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible)
    (x : ℝ) : pairDensity A B x ∈ Set.Icc (0 : ℝ) (pairCap A B) := by
  have h := affinePairDensity_cap ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd))
    (pairWidth_pos hA hB) (pairWidth_inverse_integrable hA hB) x
  exact ⟨h.1, h.2.trans (pairWidth_inverse_integral_le hA hB)⟩

theorem pairDensity_probability_density {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    (∀ x, 0 ≤ pairDensity A B x) ∧ Integrable (pairDensity A B) ∧
      (∫ x, pairDensity A B x) = 1 :=
  affinePairDensity_probability_density ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd)) (pairWidth_pos hA hB)

theorem pairDensity_test_integral {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, pairDensity A B x * φ x) =
      ∫ p : (ι → ℝ) × (ι → ℝ), ∫ u, ∫ v, φ (A.value p.1 u + B.value p.2 v)
        ∂unitScalarMeasure ∂unitScalarMeasure ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι) := by
  have h := affinePairDensity_test_integral ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd)) (pairWidth_pos hA hB) φ hφ hbound
  apply h.trans
  apply integral_congr_ae
  filter_upwards [] with p
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with v
  rw [value_eq, value_eq]
  congr 1
  simp only [Function.comp_def, Pi.add_apply]
  ring

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourSlicedProductSmoothing
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem fourDensity_cap {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) (x : ℝ) :
    fourDensity A B C D x ∈ Set.Icc (0 : ℝ) (pairCap C D) :=
  scalarDensityConvolution_cap _ _ (pairDensity_probability_density hA hB).2.1
    (pairDensity_probability_density hA hB).1 (pairDensity_probability_density hA hB).2.2
    (pairDensity_measurable C D) (pairDensity_cap hC hD) x

theorem fourDensity_lipschitz {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    LipschitzWith (pairCapNN hC hD * (2 * pairCapNN hA hB)) (fourDensity A B C D) := by
  apply scalarDensityConvolution_lipschitz _ _ _ _ (pairDensity_probability_density hA hB).2.1
    (pairDensity_measurable C D)
  · intro x
    rw [Real.norm_of_nonneg (pairDensity_cap hC hD x).1]
    exact (pairDensity_cap hC hD x).2
  · intro x y
    exact pairDensity_translation_l1_s2 hA hB x y

theorem fourDensity_probability_density {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    (∀ x, 0 ≤ fourDensity A B C D x) ∧ Integrable (fourDensity A B C D) ∧
      (∫ x, fourDensity A B C D x) = 1 := by
  have hab := pairDensity_probability_density hA hB
  have hcd := pairDensity_probability_density hC hD
  refine ⟨fun x => (fourDensity_cap hA hB hC hD x).1,
    scalarDensityConvolution_integrable _ _ (pairDensity_measurable A B)
      (pairDensity_measurable C D) hab.2.1 hcd.2.1, ?_⟩
  unfold fourDensity
  rw [scalarDensityConvolution_mass _ _ (pairDensity_measurable A B)
    (pairDensity_measurable C D) hab.2.1 hcd.2.1, hab.2.2, hcd.2.2, one_mul]

theorem fourDensity_uniform_bound {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible)
    {r : ℝ} (hr : 0 < r) (ha : r ≤ A.volumeScale) (hb : r ≤ B.volumeScale)
    (hc : r ≤ C.volumeScale) (hd : r ≤ D.volumeScale) :
    (∀ x, fourDensity A B C D x ∈ Set.Icc (0 : ℝ) (uniformCap ι r hr)) ∧
      LipschitzWith (uniformCap ι r hr * (2 * uniformCap ι r hr)) (fourDensity A B C D) := by
  have hab := pairCap_le_of_scale_lower hr ha hb
  have hcd := pairCap_le_of_scale_lower hr hc hd
  constructor
  · intro x
    exact ⟨(fourDensity_cap hA hB hC hD x).1, (fourDensity_cap hA hB hC hD x).2.trans hcd⟩
  · apply scalarDensityConvolution_lipschitz _ _ _ _ (pairDensity_probability_density hA hB).2.1
      (pairDensity_measurable C D)
    · intro x
      rw [Real.norm_of_nonneg (pairDensity_cap hC hD x).1]
      exact (pairDensity_cap hC hD x).2.trans hcd
    · intro x y
      exact (pairDensity_translation_l1_s2 hA hB x y).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab (by norm_num)) (abs_nonneg _))

theorem fourDensity_of_uniform_slice_width (B : Fin 4 → SlicedProductBlock ι)
    (hB : ∀ j, (B j).Admissible) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcoeff : ∀ j, c ≤ |(B j).coefficient|)
    (hlast : ∀ j, δ ≤ (B j).lastWidth) (hwidth : ∀ j i, δ ≤ (B j).width i) :
    let hr : 0 < c * δ ^ (Fintype.card ι + 1) := mul_pos hc (pow_pos hδ _)
    let K := uniformCap ι (c * δ ^ (Fintype.card ι + 1)) hr
    (∀ x, fourDensity (B 0) (B 1) (B 2) (B 3) x ∈ Set.Icc (0 : ℝ) K) ∧
      LipschitzWith (K * (2 * K)) (fourDensity (B 0) (B 1) (B 2) (B 3)) := by
  have hs (j : Fin 4) : c * δ ^ (Fintype.card ι + 1) ≤ (B j).volumeScale :=
    volumeScale_lower hc.le hδ.le (hcoeff j) (hlast j) (hwidth j)
  exact fourDensity_uniform_bound (hB 0) (hB 1) (hB 2) (hB 3)
    (mul_pos hc (pow_pos hδ _)) (hs 0) (hs 1) (hs 2) (hs 3)

end Erdos3.SlicedProductBlock

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

theorem unitBoxMeasure_curry (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (MeasurableEquiv.curry I J ℝ) (unitBoxMeasure (I × J))
      (Measure.pi (fun _ : I => unitBoxMeasure J)) := by
  simpa only [unitBoxMeasure_eq_pi, MeasurableEquiv.symm_symm] using
    (finiteArray_uncurry_measurePreserving (fun (_ : I) (_ : J) => unitScalarMeasure)).symm
      (MeasurableEquiv.curry I J ℝ).symm

theorem unitBoxMeasure_option (I : Type*) [Fintype I] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ))
      (unitBoxMeasure (Option I)) ((unitBoxMeasure I).prod unitScalarMeasure) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ)).symm
      ((Measure.pi (fun _ : I => unitScalarMeasure)).prod unitScalarMeasure)
      (Measure.pi (fun _ : Option I => unitScalarMeasure)) :=
    ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ)).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ : Option I => unitScalarMeasure)⟩
  simpa only [unitBoxMeasure_eq_pi, MeasurableEquiv.symm_symm] using
    h.symm (MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ)).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SpatialProductDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem pairValue_measurable (A B : SlicedProductBlock ι) : Measurable (pairValue A B) := by
  unfold pairValue value prefixProduct
  fun_prop

theorem pairSource_image {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    (pairSource ι).map (pairValue A B) = realDensityMeasure volume (pairDensity A B) := by
  have hp := pairDensity_probability_density hA hB
  apply imageLaw_eq_density_of_bounded_tests _ volume _ (pairValue_measurable A B)
    _ (pairDensity_measurable A B) hp.2.1 hp.1
  intro φ hφ hb
  have hi : Integrable (fun p => φ (pairValue A B p)) (pairSource ι) :=
    (integrable_const (1 : ℝ)).mono' (hφ.comp (pairValue_measurable A B)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hb _))
  rw [pairSource, integral_prod _ hi]
  have hi' (p : (ι → ℝ) × (ι → ℝ)) : Integrable
      (fun uv : ℝ × ℝ => φ (A.value p.1 uv.1 + B.value p.2 uv.2))
      (unitScalarMeasure.prod unitScalarMeasure) := by
    apply (integrable_const (1 : ℝ)).mono'
    · apply Measurable.aestronglyMeasurable
      apply hφ.comp
      unfold value
      fun_prop
    · exact Filter.Eventually.of_forall (fun uv => hb _)
  simp only [pairValue]
  simp_rw [integral_prod _ (hi' _)]
  exact (pairDensity_test_integral hA hB φ hφ hb).symm

theorem fourValue_measurable (A B C D : SlicedProductBlock ι) :
    Measurable (fourValue A B C D) :=
  ((pairValue_measurable A B).comp measurable_snd).add
    ((pairValue_measurable C D).comp measurable_fst)

theorem fourSource_image {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    (fourSource ι).map (fourValue A B C D) =
      realDensityMeasure volume (fourDensity A B C D) := by
  have hp := pairDensity_probability_density hA hB
  have hq := pairDensity_probability_density hC hD
  have h := scalarDensityConvolution_image_law (pairDensity A B) (pairDensity C D)
    (pairDensity_measurable A B) (pairDensity_measurable C D)
    hp.2.1 hq.2.1 hp.1 hq.1 hp.2.2 hq.2.2
  have hadd : Measurable (fun p : ℝ × ℝ => p.2 + p.1) :=
    measurable_snd.add measurable_fst
  rw [← pairSource_image hA hB, ← pairSource_image hC hD,
    Measure.map_prod_map _ _ (pairValue_measurable C D) (pairValue_measurable A B),
    Measure.map_map hadd
      ((pairValue_measurable C D).prodMap (pairValue_measurable A B))] at h
  exact h

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_measurable [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (lower width : B × F → ℝ) :
    Measurable (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem packPair_measurePreserving :
    MeasurePreserving (packPair (ι := ι))
      (Measure.pi (fun _ : Fin 2 => (unitBoxMeasure ι).prod unitScalarMeasure))
      (pairSource ι) := by
  have hs := measurePreserving_arrowProdEquivProdArrow (ι → ℝ) ℝ (Fin 2)
    (fun _ => unitBoxMeasure ι) (fun _ => unitScalarMeasure)
  exact ((measurePreserving_finTwoArrow (unitBoxMeasure ι)).prod
    (measurePreserving_finTwoArrow unitScalarMeasure)).comp hs

theorem packFour_measurePreserving :
    MeasurePreserving (packFour (ι := ι))
      (Measure.pi (fun _ : Fin 4 => (unitBoxMeasure ι).prod unitScalarMeasure))
      (fourSource ι) := by
  let μ := (unitBoxMeasure ι).prod unitScalarMeasure
  have hr := measurePreserving_piCongrLeft (fun _ : Fin 2 × Fin 2 => μ)
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm
  have hc := (finiteArray_uncurry_measurePreserving (fun (_ : Fin 2) (_ : Fin 2) => μ)).symm
    (MeasurableEquiv.curry (Fin 2) (Fin 2) ((ι → ℝ) × ℝ)).symm
  have hp := measurePreserving_pi (fun _ : Fin 2 => Measure.pi (fun _ : Fin 2 => μ))
    (fun _ : Fin 2 => pairSource ι) (fun _ => packPair_measurePreserving (ι := ι))
  have ht := measurePreserving_finTwoArrow (pairSource ι)
  have hw := Measure.measurePreserving_swap (μ := pairSource ι) (ν := pairSource ι)
  exact hw.comp (ht.comp (hp.comp (hc.comp hr)))

theorem fourBoxPacking_measurePreserving :
    MeasurePreserving (fourBoxPacking (ι := ι))
      (unitBoxMeasure (Fin 4 × Option ι)) (fourSource ι) := by
  have hc := unitBoxMeasure_curry (Fin 4) (Option ι)
  have hp := measurePreserving_pi (fun _ : Fin 4 => unitBoxMeasure (Option ι))
    (fun _ : Fin 4 => (unitBoxMeasure ι).prod unitScalarMeasure)
    (fun _ => unitBoxMeasure_option ι)
  exact packFour_measurePreserving.comp (hp.comp hc)

theorem fourBoxValue_eq (B : Fin 4 → SlicedProductBlock ι) (x : Fin 4 × Option ι → ℝ) :
    fourBoxValue B x = fourValue (B 0) (B 1) (B 2) (B 3) (fourBoxPacking x) := by
  simp [fourBoxValue, Fin.sum_univ_four, fourValue, fourBoxPacking, packFour, packPair,
    pairValue, add_assoc]

theorem fourBoxValue_image (B : Fin 4 → SlicedProductBlock ι)
    (hB : ∀ b, (B b).Admissible) :
    (unitBoxMeasure (Fin 4 × Option ι)).map (fourBoxValue B) =
      realDensityMeasure volume (fourDensity (B 0) (B 1) (B 2) (B 3)) := by
  have h := fourSource_image (hB 0) (hB 1) (hB 2) (hB 3)
  rw [← fourBoxPacking_measurePreserving.map_eq,
    Measure.map_map (fourValue_measurable _ _ _ _) fourBoxPacking_measurePreserving.measurable] at h
  simpa only [Function.comp_def, ← fourBoxValue_eq] using h

end Erdos3.SlicedProductBlock

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B ι : Type*} [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

omit [DecidableEq B] [DecidableEq ι] in
theorem principalSliceValue_eq_blocks [DecidableEq B] [DecidableEq ι]
    (c : B → ℝ) (lower width : B × Option ι → ℝ)
    (x : B × Option ι → ℝ) :
    principalSliceValue c lower width x =
      ∑ b, (principalSliceBlock c lower width b).value (fun i => x (b, some i)) (x (b, none)) := by
  unfold principalSliceValue SlicedProductBlock.value SlicedProductBlock.prefixProduct
  simp only [Fintype.prod_option, principalSliceBlock]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem principalSliceValue_four_image (c : Fin 4 → ℝ)
    (lower width : Fin 4 × Option ι → ℝ)
    (hB : ∀ b, (principalSliceBlock c lower width b).Admissible) :
    (unitBoxMeasure (Fin 4 × Option ι)).map (principalSliceValue c lower width) =
      realDensityMeasure volume
        (SlicedProductBlock.fourDensity (principalSliceBlock c lower width 0)
          (principalSliceBlock c lower width 1) (principalSliceBlock c lower width 2)
          (principalSliceBlock c lower width 3)) := by
  have he : principalSliceValue c lower width =
      SlicedProductBlock.fourBoxValue (principalSliceBlock c lower width) := by
    funext x
    exact principalSliceValue_eq_blocks c lower width x
  rw [he]
  exact SlicedProductBlock.fourBoxValue_image (principalSliceBlock c lower width) hB

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem independentShiftDensity_of_image {T X : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (z : T → ℝ) (F : X → ℝ) (hz : Measurable z) (hF : Measurable F)
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfmass : (∫ x, f x) = 1)
    (hlaw : ν.map F = realDensityMeasure volume f) :
    (μ.prod ν).map (fun p => F p.2 + z p.1) =
      realDensityMeasure volume (independentShiftDensity μ z f) := by
  apply densityMixture_image_law μ ν volume _
    ((hF.comp measurable_snd).add (hz.comp measurable_fst))
    (fun t x => f (x - z t))
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · intro t
    exact ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hfmass⟩
  · intro t
    have hshift : Measurable (fun u : ℝ => u + z t) := measurable_id.add_const _
    rw [← realDensityMeasure_map_add_right volume f (z t), ← hlaw,
      Measure.map_map hshift hF]
    rfl

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]

omit [DecidableEq J] [DecidableEq ι] in
theorem principalSumBoxSplit_measurePreserving [DecidableEq J] [DecidableEq ι] :
    MeasurePreserving (principalSumBoxSplit (J := J) (ι := ι))
      (unitBoxMeasure ((Fin 4 ⊕ J) × Option ι))
      ((unitBoxMeasure (Fin 4 × Option ι)).prod (unitBoxMeasure (J × Option ι))) := by
  exact (unitBoxMeasure_sum (Fin 4 × Option ι) (J × Option ι)).comp
    (unitBoxMeasure_reindex (Equiv.sumProdDistrib (Fin 4) J (Option ι)))

omit [DecidableEq J] [DecidableEq ι] in
theorem principalSliceValue_sum [DecidableEq J] [DecidableEq ι] (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (x : (Fin 4 ⊕ J) × Option ι → ℝ) :
    principalSliceValue c lower width x =
      principalSliceValue (fun b => c (.inl b))
        (fun p => lower (.inl p.1, p.2)) (fun p => width (.inl p.1, p.2))
        (principalSumBoxSplit x).1 +
      principalSliceValue (fun b => c (.inr b))
        (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2))
        (principalSumBoxSplit x).2 := by
  simp only [principalSliceValue, Fintype.sum_sum_type, principalSumBoxSplit]

theorem principalSliceValue_extra_image (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible) :
    (unitBoxMeasure ((Fin 4 ⊕ J) × Option ι)).map (principalSliceValue c lower width) =
      realDensityMeasure volume (principalFourRemainderDensity c lower width) := by
  let F := principalSliceValue (fun b => c (.inl b))
    (fun p => lower (.inl p.1, p.2)) (fun p => width (.inl p.1, p.2))
  let z := principalSliceValue (fun b => c (.inr b))
    (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2))
  let f := SlicedProductBlock.fourDensity
    (principalSliceBlock c lower width (.inl 0))
    (principalSliceBlock c lower width (.inl 1))
    (principalSliceBlock c lower width (.inl 2))
    (principalSliceBlock c lower width (.inl 3))
  have hF : Measurable F := principalSliceValue_measurable _ _ _
  have hz : Measurable z := principalSliceValue_measurable _ _ _
  have hf : Measurable f :=
    (SlicedProductBlock.fourDensity_lipschitz (hB 0) (hB 1) (hB 2) (hB 3)).continuous.measurable
  have hp := SlicedProductBlock.fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  have hlaw : (unitBoxMeasure (Fin 4 × Option ι)).map F = realDensityMeasure volume f :=
    principalSliceValue_four_image _ _ _ hB
  have h := independentShiftDensity_of_image (unitBoxMeasure (J × Option ι))
    (unitBoxMeasure (Fin 4 × Option ι)) z F hz hF f hf hp.2.1 hp.1 hp.2.2 hlaw
  have hs := (Measure.measurePreserving_swap
    (μ := unitBoxMeasure (Fin 4 × Option ι)) (ν := unitBoxMeasure (J × Option ι))).comp
      (principalSumBoxSplit_measurePreserving (J := J) (ι := ι))
  have hm : Measurable (fun p : (J × Option ι → ℝ) × (Fin 4 × Option ι → ℝ) =>
      F p.2 + z p.1) := (hF.comp measurable_snd).add (hz.comp measurable_fst)
  rw [← hs.map_eq, Measure.map_map hm hs.measurable] at h
  have he : (fun p => F p.2 + z p.1) ∘ (Prod.swap ∘ principalSumBoxSplit) =
      principalSliceValue c lower width := by
    funext x
    exact (principalSliceValue_sum c lower width x).symm
  rw [he] at h
  exact h

theorem principalFourRemainderDensity_bounds (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b : Fin 4, a ≤ |c (.inl b)|)
    (hw : ∀ (b : Fin 4) i, δ ≤ width (.inl b, i)) :
    let K := SlicedProductBlock.uniformCap ι (a * δ ^ (Fintype.card ι + 1))
      (mul_pos ha (pow_pos hδ _))
    (∀ x, principalFourRemainderDensity c lower width x ∈ Set.Icc (0 : ℝ) K) ∧
      LipschitzWith (K * (2 * K)) (principalFourRemainderDensity c lower width) ∧
      Integrable (principalFourRemainderDensity c lower width) ∧
      (∫ x, principalFourRemainderDensity c lower width x) = 1 := by
  dsimp only
  let B := fun b : Fin 4 => principalSliceBlock c lower width (.inl b)
  have hb := SlicedProductBlock.fourDensity_of_uniform_slice_width B hB ha hδ hc
    (fun b => hw b none) (fun b i => hw b (some i))
  have hp := SlicedProductBlock.fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  have hm := hb.2.continuous.measurable
  have hz := principalSliceValue_measurable (fun b => c (.inr b))
    (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2))
  have hi := independentShiftDensity_probability_density (unitBoxMeasure (J × Option ι))
    hz hm hp.2.1 hp.1 hp.2.2
  refine ⟨independentShiftDensity_cap _ hz hm hb.1, ?_, hi.2.1, hi.2.2⟩
  apply independentShiftDensity_lipschitz _ hz _ hb.2
  intro x
  rw [Real.norm_of_nonneg (hb.1 x).1]
  exact (hb.1 x).2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem principalSliceValue_reindex
    {B F B' F' : Type*} [Fintype B] [Fintype F] [Fintype B'] [Fintype F']
    [DecidableEq B] [DecidableEq F] [DecidableEq B'] [DecidableEq F']
    (eB : B' ≃ B) (eF : F' ≃ F) (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B' × F' → ℝ) :
    principalSliceValue c lower width (fun p => x (eB.symm p.1, eF.symm p.2)) =
      principalSliceValue (fun b => c (eB b))
        (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2)) x := by
  unfold principalSliceValue
  rw [← eB.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eB.symm_apply_apply]
  congr 1
  rw [← eF.prod_comp]
  simp only [eF.symm_apply_apply]

theorem principalSliceValue_reindex_image
    {B F B' F' : Type*} [Fintype B] [Fintype F] [Fintype B'] [Fintype F']
    [DecidableEq B] [DecidableEq F] [DecidableEq B'] [DecidableEq F']
    (eB : B' ≃ B) (eF : F' ≃ F) (c : B → ℝ) (lower width : B × F → ℝ) :
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) =
      (unitBoxMeasure (B' × F')).map (principalSliceValue (fun b => c (eB b))
        (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2))) := by
  have he := unitBoxMeasure_reindex (eB.prodCongr eF)
  rw [← he.map_eq, Measure.map_map (principalSliceValue_measurable c lower width) he.measurable]
  congr 1
  funext x
  have hr : MeasurableEquiv.piCongrLeft (fun _ : B × F => ℝ) (eB.prodCongr eF) x =
      fun p => x (eB.symm p.1, eF.symm p.2) := by
    funext p
    obtain ⟨b, hb⟩ := eB.surjective p.1
    obtain ⟨f, hf⟩ := eF.surjective p.2
    have hp : p = (eB b, eF f) := Prod.ext hb.symm hf.symm
    rw [hp]
    simpa only [Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : B × F => ℝ) (eB.prodCongr eF) x (b, f)
  change principalSliceValue c lower width _ = _
  rw [hr]
  exact principalSliceValue_reindex eB eF c lower width x

theorem reindexedSlicedPrincipalDensity_law_bounds
    {B F J I : Type*} [Fintype B] [Fintype F] [Fintype J] [Fintype I]
    [DecidableEq B] [DecidableEq F] [DecidableEq J] [DecidableEq I]
    (eB : Fin 4 ⊕ J ≃ B) (eF : Option I ≃ F)
    (c : B → ℝ) (lower width : B × F → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b : Fin 4, a ≤ |c (eB (.inl b))|)
    (hw : ∀ (b : Fin 4) i, δ ≤ width (eB (.inl b), i))
    (hl : ∀ (b : Fin 4) i, 0 ≤ lower (eB (.inl b), i)) :
    let f := reindexedSlicedPrincipalDensity eB eF c lower width
    let K := SlicedProductBlock.uniformCap I (a * δ ^ (Fintype.card I + 1)) (mul_pos ha (pow_pos hδ _))
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) = realDensityMeasure volume f ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) K) ∧ LipschitzWith (K * (2 * K)) f ∧
        Integrable f ∧ (∫ x, f x) = 1 := by
  have hadm (b : Fin 4) : (principalSliceBlock (fun b => c (eB b))
      (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2)) (.inl b)).Admissible :=
    ⟨abs_pos.mp (ha.trans_le (hc b)), fun i => hl b _, fun i => hδ.trans_le (hw b _), hδ.trans_le (hw b _)⟩
  refine ⟨?_, principalFourRemainderDensity_bounds _ _ _ hadm ha hδ hc (fun b i => hw b (eF i))⟩
  rw [principalSliceValue_reindex_image eB eF]
  exact principalSliceValue_extra_image _ _ _ hadm

theorem canonicalSlicedPrincipalDensity_law_bounds_s2_oai
    {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ) (lower width : B × F → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b, a ≤ |c b|) (hw : ∀ p, δ ≤ width p) (hl : ∀ p, 0 ≤ lower p) :
    let f := canonicalSlicedPrincipalDensity hB i c lower width
    let K := SlicedProductBlock.uniformCap {j : F // j ≠ i}
      (a * δ ^ (Fintype.card {j : F // j ≠ i} + 1)) (mul_pos ha (pow_pos hδ _))
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) = realDensityMeasure volume f ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) K) ∧ LipschitzWith (K * (2 * K)) f ∧
        Integrable f ∧ (∫ x, f x) = 1 :=
  reindexedSlicedPrincipalDensity_law_bounds (fourBlockDecomposition B hB) (Equiv.optionSubtypeNe i)
    c lower width ha hδ (fun _ => hc _) (fun _ _ => hw _) (fun _ _ => hl _)

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds_s2_oai.{u_1, u_2} := @OAI.Erdos3.canonicalSlicedPrincipalDensity_law_bounds_s2_oai.{u_1, u_2}
