-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:16.911775+00:00
-- url     : https://prove2.me/submissions/3fdfea24-6c74-47bc-8246-bb01cabe2bef

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_wt_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_summable_wt
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_radius_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_gaussian_le_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution (n : ℕ) (c t₀ C : ℝ) (hc : 0 < c) (ht₀ : 0 < t₀) :
    ∀ (X Ω : Type) [MeasurableSpace Ω] [Countable X] (Pr : Measure Ω)
      (s : Ω → X → ℝ) (p : Ω → X → Prop), (∀ x, Measurable fun ω => s ω x) →
      (∀ x, MeasurableSet {ω | p ω x}) → (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal ((|C| * (1 + (Real.sqrt t₀ ^ n)⁻¹) *
          ∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j) * (Real.sqrt t ^ n)⁻¹) := by
  intro X Ω _ _ Pr s p hsm hpm hs0 hcount t ht
  have htpos : 0 < t := ht₀.trans_le ht
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set D : ℝ := 1 + (Real.sqrt t₀ ^ n)⁻¹ with hD
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  set E : ℝ := |C| * D * B with hE
  have hE0 : 0 ≤ E := by positivity
  have hmeas : ∀ j : ℕ, Measurable fun ω => ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro j
    refine Measurable.ennreal_tsum fun x => ?_
    have hset : MeasurableSet {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} :=
      (hpm x).inter (measurableSet_le (hsm x) measurable_const)
    have heq : (fun ω => Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t}
        (fun _ => (1 : ℝ≥0∞)) x) =
        Set.indicator {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      classical
      by_cases h : p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t
      · rw [Set.indicator_of_mem (show x ∈ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_mem (show ω ∈ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_notMem (show ω ∉ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
    rw [heq]
    exact measurable_const.indicator hset
  have hpt : ∀ ω, ∑' x, Set.indicator {x | p ω x}
      (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
        {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro ω
    calc _ ≤ ∑' x, ∑' j : ℕ, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_le_tsum fun x =>
            gaussian_le_tsum c t hc htpos (s ω) (p ω) (hs0 ω) x
      _ = ∑' j : ℕ, ∑' x, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_comm
      _ = _ := by simp_rw [ENNReal.tsum_mul_left]
  have hterm : ∀ j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤
      ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) := by
    intro j
    have hR : (0 : ℝ) < 2 ^ j / Real.sqrt t := by positivity
    have hr := radius_bound n j ht₀ ht
    have hb : C * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) ≤
        ((4 : ℝ) ^ n) ^ j * E := by
      have h0 : 0 ≤ (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) := by positivity
      calc _ ≤ |C| * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h0
        _ ≤ |C| * (((4 : ℝ) ^ n) ^ j * (D * B)) :=
            mul_le_mul_of_nonneg_left hr (abs_nonneg C)
        _ = _ := by rw [hE]; ring
    calc _ ≤ ENNReal.ofReal (wt c j) * ENNReal.ofReal (((4 : ℝ) ^ n) ^ j * E) := by
          gcongr
          exact (hcount _ hR).trans (ENNReal.ofReal_le_ofReal hb)
      _ = _ := by
          rw [← ENNReal.ofReal_mul (wt_nonneg c j), mul_assoc]
  have hsum : Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j * E :=
    (summable_wt hc n).mul_right E
  calc _ ≤ ∫⁻ ω, ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_mono hpt
    _ = ∑' j : ℕ, ∫⁻ ω, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_tsum fun j => ((hmeas j).const_mul _).aemeasurable
    _ = ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr := by
        congr 1; funext j
        exact lintegral_const_mul _ (hmeas j)
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg (wt_nonneg c j) (by positivity)) hE0) hsum).symm
    _ = _ := by
        rw [tsum_mul_right, hE]
        congr 1
        ring
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
