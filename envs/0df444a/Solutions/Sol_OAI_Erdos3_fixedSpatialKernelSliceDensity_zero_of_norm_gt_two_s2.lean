-- Prove2me | solution 1 for OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:13.078977+00:00
-- url     : https://prove2.me/submissions/49834b1c-898c-42b1-8f32-fd7bd7a04da9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_bounds_s2
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_probability_density_s2
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelSliceDensity_image_law_s2

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator f) = (realDensityMeasure μ f).restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator f x)) =
      S.indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  unfold realDensityMeasure
  rw [he, withDensity_indicator hS, restrict_withDensity hS]

theorem realDensityMeasure_eq_indicator_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hf : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    realDensityMeasure μ f = realDensityMeasure μ (S.indicator f) := by
  rw [realDensityMeasure_indicator μ f hS, Measure.restrict_eq_self_of_ae_mem hf]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem continuousDensity_zero_off_closed {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SigmaFinite μ] [μ.IsOpenPosMeasure]
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {S : Set X} (hS : IsClosed S) (hs : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    ∀ x ∉ S, f x = 0 := by
  have hm := realDensityMeasure_eq_indicator_of_ae μ f hS.measurableSet hs
  have hi : Measurable (S.indicator f) := hf.measurable.indicator hS.measurableSet
  have h := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.ennreal_ofReal.aemeasurable hi.ennreal_ofReal.aemeasurable).mp hm
  have he : f =ᵐ[μ.restrict Sᶜ] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hS.measurableSet.compl] with x hx hxS
    rw [Set.indicator_of_notMem hxS, ENNReal.ofReal_zero] at hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hf0 x)
  have hall := Measure.eqOn_open_of_ae_eq he hS.isOpen_compl hf.continuousOn continuousOn_const
  exact fun x hx => hall hx

end Erdos3

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

theorem fixedSpatialKernelMap_lipschitz (W L : ℝ) (z : Option G × X → ℝ)
    (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith ((Fintype.card G : ℝ≥0) * ‖L / (1 + W)‖₊)
      (fixedSpatialKernelMap W L z) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  change |(z (none, a.1) + _ * _) - (z (none, a.1) + _ * _)| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
  have hsum : |(∑ g, z (some g, a.1) * t g) - ∑ g, z (some g, a.1) * u g| ≤
      (Fintype.card G : ℝ) * dist t u := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ g, |z (some g, a.1) * t g - z (some g, a.1) * u g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, dist t u := by
        apply Finset.sum_le_sum
        intro g _
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul_of_nonneg_right (hz g a.1) (abs_nonneg _)).trans
          (by simpa only [one_mul, Real.dist_eq] using dist_le_pi_dist t u g)
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left hsum (abs_nonneg (L / (1 + W)))
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm, Real.norm_eq_abs,
    mul_left_comm, mul_assoc] using h

theorem fixedSpatialKernelMap_lipschitz_one {W L : ℝ}
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith 1 (fixedSpatialKernelMap W L z) := by
  apply (fixedSpatialKernelMap_lipschitz W L z hz).weaken
  change (Fintype.card G : ℝ) * ‖L / (1 + W)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hL (by linarith))]
  rw [← mul_div_assoc]
  exact (div_le_one (by linarith : 0 < 1 + W)).mpr (by linarith)

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
variable {G X : Type*} [Fintype G] [Fintype X]

theorem fixedSpatialKernelMap_norm_le_two {W L : ℝ}
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (z : Option G × X → ℝ) (hz : ∀ a, |z a| ≤ 1)
    (t : G → ℝ) (ht : ‖t‖ ≤ 1) :
    ‖fixedSpatialKernelMap W L z t‖ ≤ 2 := by
  have hLip := fixedSpatialKernelMap_lipschitz_one hW hL hsize z (fun g x => hz (some g,x))
  have hd : dist (fixedSpatialKernelMap W L z t) (fixedSpatialKernelMap W L z 0) ≤ 1 := by
    have h := hLip.dist_le_mul t 0
    simp only [NNReal.coe_one, one_mul, dist_zero_right] at h
    exact h.trans ht
  have hzero : ‖fixedSpatialKernelMap W L z 0‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro a
    simpa only [fixedSpatialKernelMap, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero, Real.norm_eq_abs] using hz (none,a.1)
  calc
    _ ≤ ‖fixedSpatialKernelMap W L z t - fixedSpatialKernelMap W L z 0‖ +
        ‖fixedSpatialKernelMap W L z 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + 1 := add_le_add (by simpa only [dist_eq_norm] using hd) hzero
    _ = 2 := by norm_num

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
local notation "frame" => fixedSpatialKernelSliceFrame W L z lower width
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width false h0 hw
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width true h1 hw

local notation "density" => fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw

theorem fixedSpatialKernelSliceDensity_probability_data :
    (∀ y, 0 ≤ density y) ∧ Integrable density ∧ (∫ y, density y) = 1 :=
  fixedSpatialKernelDensity_probability_density_s2 e W L frame h0slice h1slice

theorem fixedSpatialKernelSliceDensity_bounds :
    (∀ y, density y ∈ Set.Icc (0 : ℝ)
      (fixedSpatialBlockDensityCap (fixedSpatialKernelBlockEquiv e W L frame true h1slice))) ∧
    LipschitzWith (fixedSpatialBlockDensityLipschitz
      (fixedSpatialKernelBlockEquiv e W L frame false h0slice)
      (fixedSpatialKernelBlockEquiv e W L frame true h1slice)) density :=
  fixedSpatialKernelDensity_bounds_s2 e W L frame h0slice h1slice

theorem fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2_oai
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (hl : ∀ g, 0 ≤ lower g)
    (hw0 : ∀ g, 0 ≤ width g) (hcontained : ∀ g, lower g + width g ≤ 1)
    (y : X → ℝ) (hy : 2 < ‖y‖) : density y = 0 := by
  let F := fun (t : G → ℝ) x => fixedSpatialKernelMap W L z
    (fun g => lower g + width g * t g) ⟨x, .inl ()⟩
  have hF : Measurable F := by unfold F fixedSpatialKernelMap; fun_prop
  apply continuousDensity_zero_off_closed (S := Metric.closedBall 0 2) volume _
    (fixedSpatialKernelSliceDensity_bounds e W L z lower width h0 h1 hw).2.continuous
    (fixedSpatialKernelSliceDensity_probability_data e W L z lower width h0 h1 hw).1
    Metric.isClosed_closedBall ?_ y ?_
  · rw [← fixedSpatialKernelSliceDensity_image_law_s2]
    apply (ae_map_iff hF.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
    filter_upwards [unitBoxMeasure_ae (ι := G)] with t ht
    simp only [dist_zero_right]
    have htnorm : ‖fun g => lower g + width g * t g‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro g
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hl g) (mul_nonneg (hw0 g) (ht g).1.le))]
      have hmul : width g * t g ≤ width g := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht g).2 (hw0 g)
      exact (add_le_add (le_refl (lower g)) hmul).trans (hcontained g)
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro x
    exact (norm_le_pi_norm _ ⟨x, .inl ()⟩).trans
      (fixedSpatialKernelMap_norm_le_two hW hL hsize z hz _ htnorm)
  · simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.fixedSpatialKernelSliceDensity_zero_of_norm_gt_two_s2_oai.{u_1, u_2, u_3}
