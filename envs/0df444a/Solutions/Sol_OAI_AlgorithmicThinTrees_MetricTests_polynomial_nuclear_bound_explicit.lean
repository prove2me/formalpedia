-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound_explicit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:48.309079+00:00
-- url     : https://prove2.me/submissions/33d6f661-136e-4da7-8914-e3ebef1046ae

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_AlgorithmicThinTrees_MetricProfiles_AssignedGeometry_AssignedSequence_ordered_bound
import Theorems.Thm_OAI_AlgorithmicThinTrees_MetricProfiles_AssignedGeometry_capturePackage


set_option autoImplicit false

namespace Q339.Numeric
open OAI OAI.StrongThinTree.ShortcutNumeric OAI.StrongThinTree.MultiGraph.Hierarchy

lemma le_of_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a ≤ Real.log b) : a ≤ b :=
  (Real.log_le_log_iff ha hb).1 h

/-- `log a ≤ m log 2` from `a ≤ 2^m`. -/
lemma log_le_two_pow {a : ℝ} (ha : 0 < a) (m : ℕ) (h : a ≤ (2:ℝ) ^ m) :
    Real.log a ≤ (m:ℝ) * Real.log 2 := by
  have := Real.log_le_log ha h
  rwa [Real.log_pow] at this

lemma log_le_bins {B : ℝ} (hB : 0 < B) : Real.log B ≤ 12 * Real.log 2 + B / 4096 - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < B / 4096 by positivity)
  rw [Real.log_div hB.ne' (by norm_num)] at h
  have : Real.log (4096:ℝ) = 12 * Real.log 2 := by
    rw [show (4096:ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
  linarith

/-! ### Basic facts for `x ≥ 2^2000`. Throughout, `c = log 2` and `ℓ = log x`. -/

lemma base_facts {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) :
    0 < x ∧ (32:ℝ) ≤ x ∧ 2000 * Real.log 2 ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  refine ⟨hx0, le_trans
    (le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by norm_num : 5 ≤ 2000))) hx,
    ?_⟩
  have := Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at this; push_cast at this; linarith

lemma alpha_pos {x : ℝ} (hx0 : 0 < x) : 0 < alpha x := Real.rpow_pos_of_pos hx0 _

lemma log_alpha {x : ℝ} (hx0 : 0 < x) : Real.log (alpha x) = (-4/5) * Real.log x := by
  unfold alpha; rw [Real.log_rpow hx0]

lemma bins_facts {x : ℝ} (hx0 : 0 < x) (hℓ : 0 ≤ Real.log x) :
    1 ≤ ((truncationBins (alpha x) : ℕ) : ℝ) ∧
    ((truncationBins (alpha x) : ℕ) : ℝ) * Real.log 2 < 10 * Real.log 2 + (8/5) * Real.log x ∧
    0.693 * ((truncationBins (alpha x) : ℕ) : ℝ) ≤ 10 * Real.log 2 + (8/5) * Real.log x := by
  have hc1 := Real.log_two_gt_d9
  have hc0 : 0 < Real.log 2 := by linarith
  have hyc : Real.logb 2 (256 / (alpha x) ^ 2) * Real.log 2
      = 8 * Real.log 2 + (8/5) * Real.log x := by
    rw [Real.logb, div_mul_cancel₀ _ hc0.ne',
      Real.log_div (by norm_num) (pow_pos (alpha_pos hx0) 2).ne',
      Real.log_pow, log_alpha hx0, show (256:ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    push_cast; ring
  have hy0 : 0 ≤ Real.logb 2 (256 / (alpha x) ^ 2) := by
    by_contra h; push Not at h
    have := mul_neg_of_neg_of_pos h hc0
    linarith
  have hBeq : ((truncationBins (alpha x) : ℕ) : ℝ)
      = 1 + (⌈Real.logb 2 (256 / (alpha x) ^ 2)⌉₊ : ℝ) := by
    unfold truncationBins; push_cast; ring
  have hBhi : ((truncationBins (alpha x) : ℕ) : ℝ) < 2 + Real.logb 2 (256 / (alpha x) ^ 2) := by
    rw [hBeq]; have := Nat.ceil_lt_add_one hy0; linarith
  have hBlo : 1 ≤ ((truncationBins (alpha x) : ℕ) : ℝ) := by
    rw [hBeq]
    have : (0:ℝ) ≤ (⌈Real.logb 2 (256 / (alpha x) ^ 2)⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hBc : ((truncationBins (alpha x) : ℕ) : ℝ) * Real.log 2
      < 10 * Real.log 2 + (8/5) * Real.log x := by
    have := mul_lt_mul_of_pos_right hBhi hc0
    linarith
  refine ⟨hBlo, hBc, ?_⟩
  have := mul_le_mul_of_nonneg_left (show 0.693 ≤ Real.log 2 by linarith)
    (show (0:ℝ) ≤ ((truncationBins (alpha x) : ℕ) : ℝ) by linarith)
  linarith

lemma gamma_eq (x : ℝ) : gamma x = 1 / (4 * ((truncationBins (alpha x) : ℕ) : ℝ) ^ 4) := rfl

lemma log_four : Real.log (4:ℝ) = 2 * Real.log 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma log_32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
  rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num

lemma gamma_pos' {x : ℝ} (hx0 : 0 < x) (hℓ : 0 ≤ Real.log x) : 0 < gamma x := by
  have := (bins_facts hx0 hℓ).1
  rw [gamma_eq]; positivity

lemma log_gamma {x : ℝ} (hx0 : 0 < x) (hℓ : 0 ≤ Real.log x) :
    Real.log (gamma x) = -(2 * Real.log 2 + 4 * Real.log ((truncationBins (alpha x) : ℕ) : ℝ)) := by
  have := (bins_facts hx0 hℓ).1
  rw [gamma_eq, one_div, Real.log_inv, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    log_four]
  push_cast; ring

lemma scale_pos' {x : ℝ} (hx0 : 0 < x) (hℓ : 0 ≤ Real.log x) : 0 < scale x := by
  have := alpha_pos hx0
  have := gamma_pos' hx0 hℓ
  unfold scale; positivity

lemma log_scale {x : ℝ} (hx0 : 0 < x) (hℓ : 0 ≤ Real.log x) :
    Real.log (scale x) = (-4/5) * Real.log x - 7 * Real.log 2
      - 4 * Real.log ((truncationBins (alpha x) : ℕ) : ℝ) := by
  unfold scale
  rw [Real.log_div (mul_pos (alpha_pos hx0) (gamma_pos' hx0 hℓ)).ne' (by norm_num),
    Real.log_mul (alpha_pos hx0).ne' (gamma_pos' hx0 hℓ).ne', log_alpha hx0, log_gamma hx0 hℓ,
    log_32]
  ring

/-- All the facts about `B = truncationBins (alpha x)` used below, in linear form. -/
lemma logB_facts {x : ℝ} (hx0 : 0 < x) (hℓ : 0 ≤ Real.log x) :
    0 ≤ Real.log ((truncationBins (alpha x) : ℕ) : ℝ) ∧
    Real.log ((truncationBins (alpha x) : ℕ) : ℝ) ≤ ((truncationBins (alpha x) : ℕ) : ℝ) - 1 ∧
    Real.log ((truncationBins (alpha x) : ℕ) : ℝ)
      ≤ 12 * Real.log 2 + ((truncationBins (alpha x) : ℕ) : ℝ) / 4096 - 1 := by
  have hB := (bins_facts hx0 hℓ).1
  exact ⟨Real.log_nonneg hB, Real.log_le_sub_one_of_pos (by linarith), log_le_bins (by linarith)⟩

lemma count_lower {x : ℝ} (hx0 : 0 < x) :
    (2:ℝ) ^ 20 * (1 + Real.log x / 100 - 20 * Real.log 2) ≤ (count x : ℝ) := by
  have hn1 : x ^ (1/100:ℝ) ≤ (count x : ℝ) := Nat.le_ceil _
  refine le_trans ?_ hn1
  rw [Real.rpow_def_of_pos hx0]
  have h1 : Real.exp (Real.log x * (1/100)) =
      Real.exp (20 * Real.log 2) * Real.exp (Real.log x / 100 - 20 * Real.log 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (20 * Real.log 2) = (2:ℝ) ^ 20 := by
    rw [show (20:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ 20) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [h1, h2]
  have := Real.add_one_le_exp (Real.log x / 100 - 20 * Real.log 2)
  have h3 : (0:ℝ) < 2 ^ 20 := by positivity
  have := mul_le_mul_of_nonneg_left this h3.le
  linarith

/-! ### The seven fields. -/

lemma good_small {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) :
    (scale x) ^ (1/10:ℝ) ≤ 1 / (1728 * (1024 / (1/10:ℝ) ^ 2)) := by
  obtain ⟨hx0, -, hℓ⟩ := base_facts hx
  have hc1 := Real.log_two_gt_d9
  have hℓ0 : 0 ≤ Real.log x := by linarith
  have hs0 := scale_pos' hx0 hℓ0
  have hB := logB_facts hx0 hℓ0
  apply le_of_log_le (Real.rpow_pos_of_pos hs0 _) (by norm_num)
  rw [Real.log_rpow hs0, log_scale hx0 hℓ0,
    show (1:ℝ) / (1728 * (1024 / (1/10:ℝ) ^ 2)) = (176947200:ℝ)⁻¹ by norm_num, Real.log_inv]
  have := log_le_two_pow (a := 176947200) (by norm_num) 28 (by norm_num)
  push_cast at this
  linarith [hB.1]

lemma good_assignment {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) :
    6144 / x ≤ (scale x) ^ (1 + 2 * (1/10:ℝ)) := by
  obtain ⟨hx0, -, hℓ⟩ := base_facts hx
  have hc1 := Real.log_two_gt_d9
  have hc2 := Real.log_two_lt_d9
  have hℓ0 : 0 ≤ Real.log x := by linarith
  have hs0 := scale_pos' hx0 hℓ0
  have hB := logB_facts hx0 hℓ0
  have hBl := (bins_facts hx0 hℓ0).2.2
  apply le_of_log_le (by positivity) (Real.rpow_pos_of_pos hs0 _)
  rw [Real.log_rpow hs0, log_scale hx0 hℓ0, Real.log_div (by norm_num) hx0.ne']
  have h6144 : 5 * Real.log (6144:ℝ) ≤ 63 * Real.log 2 := by
    have := Real.log_le_log (by norm_num) (show (6144:ℝ) ^ 5 ≤ 2 ^ 63 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  linarith [hB.2.2]

lemma good_rho {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) : rho x ≤ 1 / 1536 := by
  obtain ⟨-, hx2, -⟩ := base_facts hx
  unfold rho
  apply one_div_le_one_div_of_le (by norm_num)
  have : (32:ℝ) * 32 ≤ x * x := mul_le_mul hx2 hx2 (by norm_num) (by linarith only [hx2])
  rw [sq]; linarith only [this]

lemma good_log_left {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) :
    Real.logb 2 (16 / (alpha x * gamma x)) + 1 < (count x : ℝ) := by
  obtain ⟨hx0, -, hℓ⟩ := base_facts hx
  have hc1 := Real.log_two_gt_d9
  have hc2 := Real.log_two_lt_d9
  have hc0 : 0 < Real.log 2 := by linarith
  have hℓ0 : 0 ≤ Real.log x := by linarith
  have hB := logB_facts hx0 hℓ0
  have hBl := (bins_facts hx0 hℓ0).2.2
  have hα0 := alpha_pos hx0
  have hγ0 := gamma_pos' hx0 hℓ0
  have hz : Real.logb 2 (16 / (alpha x * gamma x)) * Real.log 2
      = 6 * Real.log 2 + (4/5) * Real.log x
        + 4 * Real.log ((truncationBins (alpha x) : ℕ) : ℝ) := by
    rw [Real.logb, div_mul_cancel₀ _ hc0.ne', Real.log_div (by norm_num) (by positivity),
      Real.log_mul hα0.ne' hγ0.ne', log_alpha hx0, log_gamma hx0 hℓ0,
      show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast; ring
  have hE1 : (0:ℝ) ≤ 2 ^ 20 * (1 + Real.log x / 100 - 20 * Real.log 2) - 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_left (show 0.693 ≤ Real.log 2 by linarith) hE1
  have key : Real.logb 2 (16 / (alpha x * gamma x)) * Real.log 2 <
      (2 ^ 20 * (1 + Real.log x / 100 - 20 * Real.log 2) - 1) * Real.log 2 := by
    rw [hz, mul_comm _ (Real.log 2)]; linarith [hB.2.1]
  have := lt_of_mul_lt_mul_right key hc0.le
  linarith [count_lower hx0]

lemma good_log_right {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) :
    Real.logb 2 (24 / (rho x * (scale x) ^ 2)) < (count x : ℝ) := by
  obtain ⟨hx0, -, hℓ⟩ := base_facts hx
  have hc1 := Real.log_two_gt_d9
  have hc2 := Real.log_two_lt_d9
  have hc0 : 0 < Real.log 2 := by linarith
  have hℓ0 : 0 ≤ Real.log x := by linarith
  have hB := logB_facts hx0 hℓ0
  have hBl := (bins_facts hx0 hℓ0).2.2
  have hs0 := scale_pos' hx0 hℓ0
  have hρ0 : 0 < rho x := by unfold rho; positivity
  have hρl : Real.log (rho x) = -(Real.log 2 + 2 * Real.log x) := by
    unfold rho
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have h24 : Real.log (24:ℝ) ≤ 5 * Real.log 2 := by
    have := log_le_two_pow (a := 24) (by norm_num) 5 (by norm_num)
    push_cast at this; linarith
  have hz : Real.logb 2 (24 / (rho x * (scale x) ^ 2)) * Real.log 2
      = Real.log 24 - Real.log (rho x) - 2 * Real.log (scale x) := by
    rw [Real.logb, div_mul_cancel₀ _ hc0.ne', Real.log_div (by norm_num) (by positivity),
      Real.log_mul hρ0.ne' (by positivity), Real.log_pow]
    push_cast; ring
  rw [hρl, log_scale hx0 hℓ0] at hz
  have hE1 : (0:ℝ) ≤ 2 ^ 20 * (1 + Real.log x / 100 - 20 * Real.log 2) := by linarith
  have hprod := mul_le_mul_of_nonneg_left (show 0.693 ≤ Real.log 2 by linarith) hE1
  have key : Real.logb 2 (24 / (rho x * (scale x) ^ 2)) * Real.log 2 <
      (2 ^ 20 * (1 + Real.log x / 100 - 20 * Real.log 2)) * Real.log 2 := by
    rw [hz, mul_comm _ (Real.log 2)]; linarith [hB.2.1]
  have := lt_of_mul_lt_mul_right key hc0.le
  linarith [count_lower hx0]

lemma good_coefficient {x : ℝ} (hx : (2:ℝ) ^ 2000 ≤ x) :
    coefficient x ≤ x ^ (-31/40:ℝ) / 2 := by
  obtain ⟨hx0, hx2, hℓ⟩ := base_facts hx
  have hc1 := Real.log_two_gt_d9
  have hc2 := Real.log_two_lt_d9
  have hℓ0 : 0 ≤ Real.log x := by linarith
  have hB := logB_facts hx0 hℓ0
  have hBl := (bins_facts hx0 hℓ0).2.2
  have hs0 := scale_pos' hx0 hℓ0
  have hα0 := alpha_pos hx0
  have hγ0 := gamma_pos' hx0 hℓ0
  have hp0 : 0 < x ^ (1/100:ℝ) := Real.rpow_pos_of_pos hx0 _
  have hpl : Real.log (x ^ (1/100:ℝ)) = Real.log x / 100 := by
    rw [Real.log_rpow hx0]; ring
  have hp1 : 1 ≤ x ^ (1/100:ℝ) := Real.one_le_rpow (by linarith only [hx2]) (by norm_num)
  have hn2 : (count x : ℝ) < x ^ (1/100:ℝ) + 1 := Nat.ceil_lt_add_one hp0.le
  have hy0 : 0 < x ^ (-31/40:ℝ) := Real.rpow_pos_of_pos hx0 _
  have hyl : Real.log (x ^ (-31/40:ℝ)) = (-31/40) * Real.log x := Real.log_rpow hx0 _
  have hq0 : 0 < (scale x) ^ (1/10:ℝ) := Real.rpow_pos_of_pos hs0 _
  set D : ℝ := (x / 8192) * ((scale x) ^ (1/10:ℝ) / (6912 * (1024 / (1/10:ℝ) ^ 2))) * gamma x
    with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hDl : Real.log D = Real.log x - 13 * Real.log 2 + Real.log (scale x) / 10
      - Real.log 707788800 + Real.log (gamma x) := by
    rw [hD, show (6912 * (1024 / (1/10:ℝ) ^ 2)) = 707788800 by norm_num,
      Real.log_mul (by positivity) hγ0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_div hx0.ne' (by norm_num), Real.log_div hq0.ne' (by norm_num), Real.log_rpow hs0,
      show (8192:ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    push_cast; ring
  have hK : Real.log (707788800:ℝ) ≤ 30 * Real.log 2 := by
    have := log_le_two_pow (a := 707788800) (by norm_num) 30 (by norm_num)
    push_cast at this; linarith
  have hfirst : 8 * alpha x ≤ x ^ (-31/40:ℝ) := by
    apply le_of_log_le (by positivity) hy0
    rw [Real.log_mul (by norm_num) hα0.ne', log_alpha hx0, hyl,
      show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; linarith
  have hmain : 32 * (x ^ (1/100:ℝ)) ^ 2 ≤ x ^ (-31/40:ℝ) * D := by
    apply le_of_log_le (by positivity) (by positivity)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hpl, log_32,
      Real.log_mul hy0.ne' hD0.ne', hyl, hDl, log_scale hx0 hℓ0, log_gamma hx0 hℓ0]
    push_cast
    linarith [hB.2.2]
  have hsecond : 2 * (count x : ℝ) * (count x : ℝ) / D ≤ x ^ (-31/40:ℝ) / 4 := by
    rw [div_le_iff₀ hD0]
    have hn3 : (count x : ℝ) ≤ 2 * x ^ (1/100:ℝ) := by linarith
    have hn0 : (0:ℝ) ≤ (count x : ℝ) := Nat.cast_nonneg _
    have : (count x : ℝ) * (count x : ℝ) ≤ (2 * x ^ (1/100:ℝ)) * (2 * x ^ (1/100:ℝ)) :=
      mul_le_mul hn3 hn3 hn0 (by positivity)
    have h4 : x ^ (-31/40:ℝ) / 4 * D = (x ^ (-31/40:ℝ) * D) / 4 := by ring
    rw [h4]
    linarith
  unfold coefficient
  rw [← hD]
  linarith

theorem good_explicit (x : ℝ) (hx : (2:ℝ) ^ 2000 ≤ x) :
    OAI.StrongThinTree.ShortcutNumeric.GoodParameters x :=
  ⟨le_trans (by norm_num) (base_facts hx).2.1, good_small hx, good_assignment hx, good_rho hx,
    good_log_left hx, good_log_right hx, good_coefficient hx⟩

end Q339.Numeric

section
-- module Solutions.OAIQ241_TT.ThinTrees_Coarea
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uE uV2 uE2 uV3 uE3 uI uI2 uI3

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma integrable_interval_indicator (a b c : ℝ) :
    Integrable ((Set.Ioc a b).indicator (fun _ : ℝ => c)) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))

lemma integral_interval_indicator (a b c : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, (Set.Ioc a b).indicator (fun _ => c) t) = (b-a)*c := by
  rw [integral_indicator_const c measurableSet_Ioc, Real.volume_real_Ioc,
    max_eq_left (sub_nonneg.mpr hab), smul_eq_mul]

lemma threshold_interval {x y t : ℝ} :
    ((x < t ∧ ¬ y < t) ∨ (y < t ∧ ¬ x < t)) ↔ t ∈ Set.Ioc (min x y) (max x y) := by
  simp only [Set.mem_Ioc, min_lt_iff, le_max_iff, not_lt]
  constructor
  · rintro (h | h)
    · exact ⟨Or.inl h.1, Or.inr h.2⟩
    · exact ⟨Or.inr h.1, Or.inl h.2⟩
  · rintro ⟨h | h, h' | h'⟩ <;> first | (exfalso; linarith) | exact Or.inl ⟨h, h'⟩ | exact Or.inr ⟨h, h'⟩

lemma finite_coarea {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    (∫ t : ℝ, (((univ.filter (fun e =>
      (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) =
      ∑e, |f (u e)-f (v e)| := by
  have heq (t : ℝ) :
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ)) =
      ∑e, (Set.Ioc (min (f (u e)) (f (v e)))
        (max (f (u e)) (f (v e)))).indicator (fun _ : ℝ => (1:ℝ)) t := by
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro e he
    rw [Set.indicator_apply]
    simp only [threshold_interval]
    split_ifs <;> norm_num
  simp_rw [heq]
  rw [integral_finsetSum _ (fun e _ => integrable_interval_indicator _ _ _)]
  apply sum_congr rfl
  intro e he
  rw [integral_interval_indicator _ _ _ min_le_max, mul_one]
  simpa only [abs_sub_comm] using (max_sub_min_eq_abs (f (u e)) (f (v e)))

lemma integrable_cut_card {V : Type uV2} {E : Type uE2} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    Integrable (fun t : ℝ =>
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) := by
  have hi := integrable_finsetSum univ
    (fun e _ => integrable_interval_indicator (min (f (u e)) (f (v e)))
      (max (f (u e)) (f (v e))) 1)
  apply hi.congr
  filter_upwards with t
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro e he
  rw [Set.indicator_apply]
  simp only [threshold_interval]
  split_ifs <;> norm_num

lemma cut_range_bound {V : Type uV3} {E : Type uE3} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) {a b k : ℝ} (hab : a ≤ b)
    (hcut : ∀t ∈ Set.Ioc a b, k ≤
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) :
    k*(b-a) ≤ ∑e, |f (u e)-f (v e)| := by
  have hh := integral_mono (integrable_interval_indicator a b k)
    (integrable_cut_card u v f) (show (Set.Ioc a b).indicator (fun _ : ℝ => k) ≤
      (fun t : ℝ => (((univ.filter (fun e =>
        (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) by
        intro t
        by_cases ht : t ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem ht]
          exact hcut t ht
        · rw [Set.indicator_of_notMem ht]
          positivity)
  rw [integral_interval_indicator a b k hab, finite_coarea] at hh
  simpa only [mul_comm] using hh

lemma clamp_eq_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) : clamp a b x = a := by
  simp [clamp, max_eq_left hx, min_eq_right hab]

lemma clamp_eq_right {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) : clamp a b x = b := by
  simp [clamp, max_eq_right (hab.trans hx), min_eq_left hx]

lemma clamp_bounds {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ clamp a b x ∧ clamp a b x ≤ b := by
  exact ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩

lemma clamp_lt_iff {a b x t : ℝ} (ht : t ∈ Set.Ioc a b) :
    clamp a b x < t ↔ x < t := by
  simp only [clamp, min_lt_iff, max_lt_iff]
  constructor
  · rintro (h | h)
    · linarith [ht.2]
    · exact h.2
  · intro h
    exact Or.inr ⟨ht.1, h⟩

end
end StrongThinTree.Geometry

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m : ℕ} (G : MultiGraph n m)

lemma clamped_variation_lower {k : ℕ} (hk : G.EdgeConnected k)
    (f : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hu : ∃u, f u ≤ a) (hv : ∃v, b ≤ f v) :
    (k : ℝ)*(b-a) ≤ ∑e : Fin m,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  classical
  apply cut_range_bound G.left G.right (fun v => clamp a b (f v)) hab
  intro t ht
  let S := univ.filter (fun v => f v < t)
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := hu
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, lt_of_le_of_lt hu ht.1⟩⟩
  have hproper : S ≠ univ := by
    obtain ⟨v, hv⟩ := hv
    intro heq
    have hh : v ∈ S := heq.symm ▸ mem_univ v
    have := (mem_filter.mp hh).2
    linarith [ht.2]
  have hc := hk S hne hproper
  have hset : (univ.filter (fun e =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) = G.cut univ S := by
    ext e
    simp only [S, cut, mem_filter, mem_univ, true_and, clamp_lt_iff ht]
  rw [hset]
  exact_mod_cast hc

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma clamp_mono {a b x y : ℝ} (hxy : x ≤ y) : clamp a b x ≤ clamp a b y :=
  min_le_min_left _ (max_le_max_left _ hxy)

lemma clipped_affine_interval_increasing {a b x y : ℝ} (hab : a ≤ b) (hxy : x < y) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  by_cases heq : clamp a b x = clamp a b y
  · exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp [heq],by simp⟩
  have hAB := lt_of_le_of_ne (clamp_mono hxy.le) heq
  have hAx := clamp_bounds hab x
  have hBy := clamp_bounds hab y
  have hx : x < b := by
    by_contra h
    have hh := clamp_eq_right hab (not_lt.mp h)
    linarith
  have hy : a < y := by
    by_contra h
    have hh := clamp_eq_left hab (not_lt.mp h)
    linarith
  have hxA : x ≤ clamp a b x := by
    rw [clamp, min_eq_right (max_le hab hx.le)]
    exact le_max_right _ _
  have hBy' : clamp a b y ≤ y := by
    rw [clamp, max_eq_right hy.le]
    exact min_le_right _ _
  let s := y-x
  have hs : 0 < s := sub_pos.mpr hxy
  let l := (clamp a b x-x)/s
  let r := (clamp a b y-x)/s
  have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hxA) hs.le
  have hr : r ≤ 1 := (div_le_one hs).mpr (by dsimp [s] <;> linarith)
  have hlr : l ≤ r := (div_le_div_iff_of_pos_right hs).mpr (by linarith)
  have hlmul : l*s = clamp a b x-x := div_mul_cancel₀ _ hs.ne'
  have hrmul : r*s = clamp a b y-x := div_mul_cancel₀ _ hs.ne'
  refine ⟨l,r,hl,hlr,hr,?_,?_⟩
  · rw [abs_of_nonpos (by linarith : clamp a b x-clamp a b y ≤ 0),
      abs_of_pos (sub_pos.mpr hxy)]
    dsimp [s] at hlmul hrmul
    nlinarith
  · intro t ht
    have hlt := mul_lt_mul_of_pos_right ht.1 hs
    have htr := mul_lt_mul_of_pos_right ht.2 hs
    dsimp [s] at hlt htr hlmul hrmul
    constructor <;> nlinarith

lemma clipped_affine_interval {a b x y : ℝ} (hab : a ≤ b) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact clipped_affine_interval_increasing hab hxy
  · subst y
    exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp,by simp⟩
  · obtain ⟨l,r,hl,hlr,hr,heq,h⟩ := clipped_affine_interval_increasing hab hxy
    refine ⟨1-r,1-l,by linarith,by linarith,by linarith,?_,?_⟩
    · rw [abs_sub_comm, heq, abs_sub_comm x y]
      congr 1
      ring
    · intro t ht
      have hh := h (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      constructor <;> nlinarith [hh.1,hh.2]

lemma clamped_affine_disjoint_sum {I : Type uI} [Fintype I]
    (a b x y : I → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hab : ∀i, a i ≤ b i) (hslope : ∀i, |y i-x i| ≤ L)
    (hdis : ∀ i j, i ≠ j → ∀t ∈ Set.Ioo (0:ℝ) 1,
      ¬(a i < x i+t*(y i-x i) ∧ x i+t*(y i-x i)<b i ∧
        a j < x j+t*(y j-x j) ∧ x j+t*(y j-x j)<b j)) :
    ∑i, |clamp (a i) (b i) (x i)-clamp (a i) (b i) (y i)| ≤ L := by
  classical
  choose l r hl hlr hr heq hactive using fun i =>
    clipped_affine_interval (x:=x i) (y:=y i) (hab i)
  have hsub : (⋃i, Set.Ioo (l i) (r i)) ⊆ Set.Ioo (0:ℝ) 1 := by
    rintro t ⟨_,⟨i,rfl⟩,ht⟩
    exact ⟨lt_of_le_of_lt (hl i) ht.1,lt_of_lt_of_le ht.2 (hr i)⟩
  have hd : Pairwise (fun i j => Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    exact hdis i j hij t ⟨lt_of_le_of_lt (hl i) hti.1,
      lt_of_lt_of_le hti.2 (hr i)⟩ ⟨(hactive i t hti).1,(hactive i t hti).2,
        (hactive j t htj).1,(hactive j t htj).2⟩
  have hv := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioo])
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ioo)
      (fun _ => by simp [Real.volume_Ioo]), Real.volume_real_Ioo] at hv
  simp only [Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr (hlr _))] at hv
  have hsum : ∑i, (r i-l i) ≤ 1 := by simpa using hv
  calc
    _ = ∑i, |y i-x i| *(r i-l i) := sum_congr rfl (fun i _ => heq i)
    _ ≤ ∑i, L*(r i-l i) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hslope i) (sub_nonneg.mpr (hlr i)))
    _ = L*∑i, (r i-l i) := (mul_sum _ _ _).symm
    _ ≤ L*1 := mul_le_mul_of_nonneg_left hsum hL
    _ = L := mul_one L

end
end StrongThinTree.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Capture
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
open scoped Classical
variable {n m : ℕ} (H : Hierarchy n) (G : MultiGraph n m)

lemma boundary_owner_unique {A B : Finset (Fin n)} {u v : Fin n}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes) (hAr : A ≠ univ) (hBr : B ≠ univ)
    (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hvPA : v ∈ H.parent A) (hvPB : v ∈ H.parent B) : A = B := by
  rcases H.laminar A hA B hB with hAB | hBA | hdis
  · by_contra hne
    have hp := H.parent_minimal A hA hAr B hB (Finset.ssubset_iff_subset_ne.mpr ⟨hAB,hne⟩)
    exact hvB (hp hvPA)
  · by_contra hne
    have hp := H.parent_minimal B hB hBr A hA (Finset.ssubset_iff_subset_ne.mpr ⟨hBA,Ne.symm hne⟩)
    exact hvA (hp hvPB)
  · exact (Finset.disjoint_left.mp hdis huA huB).elim

lemma parentBoundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ) (e : Fin m) :
    (T.filter (fun t => e ∈ H.parentBoundary G t)).card ≤ 2 := by
  let S := T.filter (fun t => e ∈ H.parentBoundary G t)
  let L := S.filter (fun t => G.left e ∈ t)
  let R := S.filter (fun t => G.right e ∈ t)
  have hL : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hlA⟩ := mem_filter.mp hA
    obtain ⟨hB,hlB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hrA : G.right e ∉ A := by rcases hcutA with hh | hh; exact hh.2; exact (hh.2 hlA).elim
    have hrB : G.right e ∉ B := by rcases hcutB with hh | hh; exact hh.2; exact (hh.2 hlB).elim
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hlA hlB hrA hrB ((G.mem_inducedEdges _ _).mp hePA).2 ((G.mem_inducedEdges _ _).mp hePB).2
  have hR : R.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hrA⟩ := mem_filter.mp hA
    obtain ⟨hB,hrB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hlA : G.left e ∉ A := by rcases hcutA with hh | hh; exact (hh.2 hrA).elim; exact hh.2
    have hlB : G.left e ∉ B := by rcases hcutB with hh | hh; exact (hh.2 hrB).elim; exact hh.2
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hrA hrB hlA hlB ((G.mem_inducedEdges _ _).mp hePA).1 ((G.mem_inducedEdges _ _).mp hePB).1
  have hsub : S ⊆ L∪R := by
    intro A hA
    have hc := (mem_filter.mp (mem_filter.mp hA).2).2
    rcases hc with hh | hh
    · exact mem_union_left _ (mem_filter.mpr ⟨hA,hh.1⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hA,hh.1⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Density
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT uE uI uI2 uA uB

section
open scoped Classical
open Matrix

namespace StrongThinTree.BagDensity
noncomputable section
open Finset
open scoped Classical
variable {T : Type uT} {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in
lemma sum_square_bound (F : Finset E) (a : E → ℝ) {c : ℝ}
    (hc : ∀e ∈ F, (a e)^2 ≤ c) : (∑e ∈ F, a e)^2 ≤ c*(F.card : ℝ)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun _ => (1:ℝ)) a
  have hs : (∑e ∈ F, (a e)^2) ≤ (F.card : ℝ)*c := by simpa using sum_le_sum hc
  simp only [one_pow,sum_const,nsmul_eq_mul,mul_one,one_mul] at hcs
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg F.card : (0:ℝ) ≤ _)
  nlinarith

omit [DecidableEq E] in
lemma local_density (O F : Finset E) (a d : E → ℝ) {α γ c₁ c₂ : ℝ}
    (hF : F ⊆ O) (hFn : F.Nonempty) (hα : 0 < α) (hγ : 0 < γ)
    (hd : ∀e ∈ O, 0 ≤ d e) (hmax : ∀e ∈ F, (a e)^2 ≤ 4*c₁)
    (hmin : ∀e ∈ F, c₂/4 ≤ d e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    (hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ F, a e)^2) :
    α*γ*(O.card : ℝ)*c₂ ≤ 16*c₁*F.card := by
  have hFc : (0:ℝ) < F.card := by exact_mod_cast card_pos.mpr hFn
  have hOc : (0:ℝ) ≤ O.card := Nat.cast_nonneg _
  have hsum : (F.card : ℝ)*(c₂/4) ≤ ∑e ∈ O, d e := by
    calc
      _ = ∑_e ∈ F, c₂/4 := by simp
      _ ≤ ∑e ∈ F, d e := sum_le_sum hmin
      _ ≤ ∑e ∈ O, d e := sum_le_sum_of_subset_of_nonneg hF (fun e he _ => hd e he)
  have hh1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ γ*α*(O.card : ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hbad hγ.le
  have hu := sum_square_bound F a hmax
  apply (mul_le_mul_iff_right₀ hFc).mp
  nlinarith

end
end StrongThinTree.BagDensity

namespace StrongThinTree.ScaleSelection
noncomputable section
open Finset
open scoped Classical

lemma integer_dyadic {x : ℝ} (hx : 0 < x) :
    2^(⌊Real.logb 2 x⌋ : ℝ) ≤ x ∧ x < 2*2^(⌊Real.logb 2 x⌋ : ℝ) := by
  have h1 := (Real.le_logb_iff_rpow_le (by norm_num) hx).mp (Int.floor_le (Real.logb 2 x))
  have h2 := (Real.logb_lt_iff_lt_rpow (by norm_num) hx).mp (Int.lt_floor_add_one (Real.logb 2 x))
  rw [Real.rpow_add (by norm_num),Real.rpow_one] at h2
  constructor
  · exact h1
  · nlinarith only [h2]

lemma integer_dyadic_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ⌊Real.logb 2 x⌋ ≤ ⌊Real.logb 2 y⌋ :=
  Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) hx hxy)

lemma integer_scale_offset {x y K : ℝ} {L : ℕ}
    (hx : 0 < x) (hxy : x ≤ y) (hK : y ≤ K*x)
    (hL : Real.logb 2 K+1 < L) :
    0 ≤ ⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ ∧
      ⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ < L := by
  have hy : 0 < y := hx.trans_le hxy
  have hK0 : 0 < K := by nlinarith only [hK,hy,hx]
  have hlogs : Real.logb 2 y ≤ Real.logb 2 K+Real.logb 2 x := by
    rw [←Real.logb_mul hK0.ne' hx.ne']
    exact Real.logb_le_logb_of_le (by norm_num) hy hK
  constructor
  · exact sub_nonneg.mpr (integer_dyadic_mono hx hxy)
  · have h1 := Int.floor_le (Real.logb 2 y)
    have h2 := Int.lt_floor_add_one (Real.logb 2 x)
    have hh : ((⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ : ℤ) : ℝ) < L := by
      push_cast
      linarith only [h1,h2,hlogs,hL]
    exact_mod_cast hh

lemma select_fibers {I : Type uI2} {A : Type uA} {B : Type uB} [DecidableEq I] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Nonempty B]
    (T : Finset I) (a : I → A) (b : I → B) (w : I → ℝ) :
    ∃choice : A → B,
      (∑i ∈ T, w i)/(Fintype.card B : ℝ) ≤
        ∑i ∈ T.filter (fun i => b i = choice (a i)), w i := by
  have hB : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  have hex : ∀x : A, ∃y : B,
      (∑i ∈ T.filter (fun i => a i=x), w i)/(Fintype.card B : ℝ) ≤
        ∑i ∈ (T.filter (fun i => a i=x)).filter (fun i => b i=y), w i := by
    intro x
    obtain ⟨y,hy,hgain⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := T.filter (fun i => a i=x)) (t := univ) (f := b) (w := w)
      (fun _ _ => mem_univ _) univ_nonempty
      (b := (∑i ∈ T.filter (fun i => a i=x), w i)/(Fintype.card B : ℝ)) (by
        simp only [card_univ,nsmul_eq_mul]
        exact (mul_div_cancel₀ _ hB.ne').le)
    exact ⟨y,hgain⟩
  choose choice hchoice using hex
  refine ⟨choice,?_⟩
  have hs := sum_le_sum (s := T.image a) (fun x hx => hchoice x)
  rw [←sum_div] at hs
  have hleft : (∑x ∈ T.image a, ∑i ∈ T.filter (fun i => a i=x), w i) = ∑i ∈ T, w i := by
    exact sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem a hi) w
  rw [hleft] at hs
  have hright : (∑x ∈ T.image a, ∑i ∈ (T.filter (fun i => a i=x)).filter
      (fun i => b i=choice x), w i) = ∑i ∈ T.filter (fun i => b i=choice (a i)), w i := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single (a i)]
    · simp
    · intro x hx hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (mem_image_of_mem a hi)).elim
  rw [hright] at hs
  exact hs

lemma residue_spacing {H : ℕ} (_hH : 0 < H) {n n' : ℤ}
    (hlt : n' < n) (hmod : n'%H = n%H) : n' ≤ n-H := by
  have hd : (H:ℤ) ∣ n-n' := Int.ModEq.dvd hmod
  have hh := Int.le_of_dvd (sub_pos.mpr hlt) hd
  omega

lemma separated_scales {s ρ : ℝ} {H : ℕ} {n n' : ℤ}
    (hs : 0 < s) (hρ : 0 < ρ)
    (hH : Real.logb 2 (24/(ρ*s^2)) < H)
    (hgap : n' ≤ n-H) : 24*2^(n':ℝ)/s < ρ*s*2^(n:ℝ) := by
  have hpow : 24/(ρ*s^2) < (2:ℝ)^(H:ℝ) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)).mp hH
  have hgapR : (n':ℝ)+(H:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : n'+H ≤ n)
  have hle : (2:ℝ)^(n':ℝ)*(2:ℝ)^(H:ℝ) ≤ (2:ℝ)^(n:ℝ) := by
    rw [←Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hgapR
  have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (n':ℝ)
  have hh := (div_lt_iff₀ (show 0 < ρ*s^2 by positivity)).mp hpow
  have hm := mul_lt_mul_of_pos_left hh hp
  have hm' := mul_le_mul_of_nonneg_right hle (show 0 ≤ ρ*s^2 by positivity)
  apply (div_lt_iff₀ hs).mpr
  nlinarith only [hm,hm']

end
end StrongThinTree.ScaleSelection

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Truncation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section
open scoped Classical
open Matrix

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in

lemma sum_sq_le_card_mul_sum_sq (S : Finset E) (a : E → ℝ) :
    (∑e ∈ S, a e)^2 ≤ (S.card : ℝ)*(∑e ∈ S, (a e)^2) := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) a

lemma two_truncations (S : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (_hα1 : α ≤ 1) (hS : S.Nonempty)
    (ha : ∀e ∈ S, 0 ≤ a e) (hsq : ∀e ∈ S, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ S, a e)
    (hbad : α*(S.card : ℝ)*(∑e ∈ S, d e) ≤ (∑e ∈ S, a e)^2) :
    let μ := (∑e ∈ S, a e)/(S.card : ℝ)
    ∃R : Finset E, R ⊆ S ∧
      (∑e ∈ S, a e)/2 ≤ ∑e ∈ R, a e ∧
      ∀e ∈ R, μ^2/16 ≤ (a e)^2 ∧ (a e)^2 ≤ d e ∧ d e ≤ 16*μ^2/α^2 := by
  let M : ℝ := S.card
  let A : ℝ := ∑e ∈ S, a e
  let μ := A/M
  have hM : 0 < M := by dsimp [M]; exact_mod_cast card_pos.mpr hS
  have hA : 0 < A := hpos
  have hμ : 0 < μ := div_pos hA hM
  have hμM : μ*M = A := div_mul_cancel₀ _ hM.ne'
  have hbad' : α*(∑e ∈ S, d e) ≤ M*μ^2 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    change α*M*(∑e ∈ S, d e) ≤ A^2 at hbad
    nlinarith [sq_nonneg (μ*M-A)]
  let L := S.filter (fun e => a e < μ/4)
  let H := S.filter (fun e => 16*μ^2/α^2 < d e)
  let R := S\(L∪H)
  have hd : ∀e ∈ S, 0 ≤ d e := fun e he => (sq_nonneg _).trans (hsq e he)
  have hLsum : (∑e ∈ L, a e) ≤ A/4 := by
    calc
      _ ≤ ∑_e ∈ L, μ/4 := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ = (L.card : ℝ)*μ/4 := by simp <;> ring
      _ ≤ M*μ/4 := by
        have hh : (L.card : ℝ) ≤ M := by
          change (L.card : ℝ) ≤ (S.card : ℝ)
          exact_mod_cast card_le_card (show L ⊆ S from filter_subset _ _)
        nlinarith
      _ = A/4 := by rw [mul_comm M,hμM]
  have hHmass : (H.card : ℝ)*(16*μ^2/α^2) ≤ ∑e ∈ S, d e := by
    calc
      _ = ∑_e ∈ H, 16*μ^2/α^2 := by simp
      _ ≤ ∑e ∈ H, d e := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ ≤ ∑e ∈ S, d e := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hd e he)
  have hHcard : (H.card : ℝ) ≤ α*M/16 := by
    have hc := mul_le_mul_of_nonneg_left hHmass hα.le
    have hμ2 : 0 < μ^2 := sq_pos_of_pos hμ
    have heq : α*(H.card : ℝ)*(16*μ^2/α^2) = (H.card : ℝ)*16*μ^2/α := by field_simp
    have hh : (H.card : ℝ)*16*μ^2/α ≤ M*μ^2 := by
      calc
        _ = α*((H.card : ℝ)*(16*μ^2/α^2)) := by rw [←mul_assoc,heq]
        _ ≤ α*(∑e ∈ S, d e) := hc
        _ ≤ M*μ^2 := hbad'
    have hh' := (div_le_iff₀ hα).mp hh
    nlinarith
  have hHsq : (∑e ∈ H, a e)^2 ≤ (A/4)^2 := by
    have hcs := sum_sq_le_card_mul_sum_sq H a
    have hs : ∑e ∈ H, (a e)^2 ≤ ∑e ∈ S, d e :=
      (sum_le_sum (fun e he => hsq e (mem_filter.mp he).1)).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hd e he))
    have hD0 : 0 ≤ ∑e ∈ S, d e := sum_nonneg hd
    have hh := mul_le_mul_of_nonneg_right hHcard hD0
    have hh' := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg H.card : (0:ℝ) ≤ _)
    have hb := mul_le_mul_of_nonneg_left hbad' hM.le
    nlinarith [sq_nonneg (μ*M-A)]
  have hHsum : (∑e ∈ H, a e) ≤ A/4 := by nlinarith [sum_nonneg (s := H) (fun e he => ha e (mem_filter.mp he).1)]
  have hU : L∪H ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  have hsum : ∑e ∈ S, a e = (∑e ∈ R, a e)+(∑e ∈ L∪H, a e) := (sum_sdiff hU).symm
  have hUH : ∑e ∈ L∪H, a e ≤ (∑e ∈ L, a e)+(∑e ∈ H, a e) := by
    have he := sum_union_inter (s₁ := L) (s₂ := H) (f := a)
    have hi : 0 ≤ ∑e ∈ L∩H, a e := sum_nonneg (fun e he => ha e (hU (mem_union_left _ (mem_inter.mp he).1)))
    linarith
  refine ⟨R,sdiff_subset,?_,?_⟩
  · change A/2 ≤ _
    change A = _ at hsum
    linarith
  · intro e he
    obtain ⟨heS,heU⟩ := mem_sdiff.mp he
    have hle : μ/4 ≤ a e := le_of_not_gt (fun hh => heU (mem_union_left _ (mem_filter.mpr ⟨heS,hh⟩)))
    have hde : d e ≤ 16*μ^2/α^2 := le_of_not_gt (fun hh => heU (mem_union_right _ (mem_filter.mpr ⟨heS,hh⟩)))
    exact ⟨by change μ^2/16 ≤ _; nlinarith [ha e heS],hsq e heS,hde⟩

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE2} [DecidableEq E]

lemma dyadic_interval {L x : ℝ} (hL : 0 < L) (hx : L ≤ x) :
    (2:ℝ)^(dyadicIndex L x : ℝ)*L ≤ x ∧
      x < 2*((2:ℝ)^(dyadicIndex L x : ℝ)*L) := by
  have hratio : 1 ≤ x/L := (le_div_iff₀ hL).mpr (by simpa)
  have hp : 0 < x/L := lt_of_lt_of_le zero_lt_one hratio
  have hg : 0 ≤ Real.logb 2 (x/L) := Real.logb_nonneg (by norm_num) hratio
  constructor
  · exact (le_div_iff₀ hL).mp ((Real.le_logb_iff_rpow_le (by norm_num) hp).mp (Nat.floor_le hg))
  · have hh := (Real.logb_lt_iff_lt_rpow (by norm_num) hp).mp (Nat.lt_floor_add_one (Real.logb 2 (x/L)))
    rw [Real.rpow_add (by norm_num),Real.rpow_one] at hh
    have hh' := (div_lt_iff₀ hL).mp hh
    dsimp [dyadicIndex]
    nlinarith

lemma dyadicIndex_lt {L U x : ℝ} {J : ℕ} (hL : 0 < L) (hx : L ≤ x) (hU : x ≤ U)
    (hJ : Real.logb 2 (U/L) < J) : dyadicIndex L x < J := by
  have hr : 1 ≤ x/L := (le_div_iff₀ hL).mpr (by simpa)
  apply (Nat.floor_lt (Real.logb_nonneg (by norm_num) hr)).mpr
  exact (Real.logb_le_logb_of_le (by norm_num) (lt_of_lt_of_le zero_lt_one hr)
    ((div_le_div_iff_of_pos_right hL).mpr hU)).trans_lt hJ

lemma same_dyadic_ratio {L x y : ℝ} (hL : 0 < L) (hx : L ≤ x) (hy : L ≤ y)
    (heq : dyadicIndex L x = dyadicIndex L y) : x < 2*y := by
  have hh := (dyadic_interval hL hx).2
  rw [heq] at hh
  exact hh.trans_le (mul_le_mul_of_nonneg_left (dyadic_interval hL hy).1 (by norm_num))

omit [DecidableEq E] in

lemma dyadic_pair (R : Finset E) (a b w : E → ℝ) {L U : ℝ} {J : ℕ}
    (hL : 0 < L) (hJ : 0 < J) (hj : Real.logb 2 (U/L) < J)
    (ha : ∀e ∈ R, L ≤ a e ∧ a e ≤ U) (hb : ∀e ∈ R, L ≤ b e ∧ b e ≤ U)
    (hpos : 0 < ∑e ∈ R, w e) :
    ∃B : Finset E, B.Nonempty ∧ B ⊆ R ∧
      (∑e ∈ R, w e)/(J:ℝ)^2 ≤ ∑e ∈ B, w e ∧
      ∀e ∈ B, ∀f ∈ B, a e < 2*a f ∧ b e < 2*b f := by
  let f := fun e => (dyadicIndex L (a e),dyadicIndex L (b e))
  let T := (range J)×ˢ(range J)
  have hT : T.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr hJ,mem_range.mpr hJ⟩⟩
  have hf : ∀e ∈ R, f e ∈ T := by
    intro e he
    exact mem_product.mpr ⟨mem_range.mpr (dyadicIndex_lt hL (ha e he).1 (ha e he).2 hj),
      mem_range.mpr (dyadicIndex_lt hL (hb e he).1 (hb e he).2 hj)⟩
  have hJ0 : (0:ℝ) < J := by exact_mod_cast hJ
  obtain ⟨i,hi,hgain⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (w := w) hf hT
    (b := (∑e ∈ R, w e)/(J:ℝ)^2) (by
      have hh : (T.card : ℝ) = (J:ℝ)^2 := by simp [T,pow_two]
      rw [nsmul_eq_mul,hh,mul_div_cancel₀ _ (ne_of_gt (sq_pos_of_pos hJ0))])
  refine ⟨R.filter (fun e => f e=i),?_,filter_subset _ _,hgain,?_⟩
  · apply card_pos.mp
    by_contra hh
    have he : (R.filter (fun e => f e=i)) = ∅ := card_eq_zero.mp (by omega)
    rw [he,sum_empty] at hgain
    exact (not_le_of_gt (div_pos hpos (sq_pos_of_pos hJ0))) hgain
  · intro e he g hg
    obtain ⟨he,hfe⟩ := mem_filter.mp he
    obtain ⟨hg,hfg⟩ := mem_filter.mp hg
    have heq := hfe.trans hfg.symm
    exact ⟨same_dyadic_ratio hL (ha e he).1 (ha g hg).1 (congrArg Prod.fst heq),
      same_dyadic_ratio hL (hb e he).1 (hb g hg).1 (congrArg Prod.snd heq)⟩

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE3} [DecidableEq E]

lemma homogeneous_subset (S : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : S.Nonempty)
    (ha : ∀e ∈ S, 0 ≤ a e) (hsq : ∀e ∈ S, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ S, a e)
    (hbad : α*(S.card : ℝ)*(∑e ∈ S, d e) ≤ (∑e ∈ S, a e)^2) :
    let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
    ∃B : Finset E, B.Nonempty ∧ B ⊆ S ∧
      (∑e ∈ S, a e)^2/(4*(J:ℝ)^4) ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 0 < (a e)^2) ∧
      ∀e ∈ B, ∀f ∈ B, (a e)^2 < 2*(a f)^2 ∧ d e < 2*d f := by
  let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
  let A := ∑e ∈ S, a e
  let μ := A/(S.card : ℝ)
  have hM : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  have hμ : 0 < μ := div_pos hpos hM
  obtain ⟨R,hRS,hRsum,hR⟩ := two_truncations S a d hα hα1 hS ha hsq hpos hbad
  have hRpos : 0 < ∑e ∈ R, a e := by linarith
  have hJ : 0 < J := by dsimp [J]; omega
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have hj : Real.logb 2 ((16*μ^2/α^2)/(μ^2/16)) < J := by
    have he : (16*μ^2/α^2)/(μ^2/16) = 256/α^2 := by field_simp <;> ring
    rw [he]
    have hh := Nat.le_ceil (Real.logb 2 (256/α^2))
    dsimp [J]
    push_cast
    linarith
  obtain ⟨B,hB,hBR,hgain,hratio⟩ := dyadic_pair R (fun e => (a e)^2) d a
    (show 0 < μ^2/16 by positivity) hJ hj
    (fun e he => ⟨(hR e he).1,(hR e he).2.1.trans (hR e he).2.2⟩)
    (fun e he => ⟨(hR e he).1.trans (hR e he).2.1,(hR e he).2.2⟩) hRpos
  refine ⟨B,hB,hBR.trans hRS,?_,?_,hratio⟩
  · change A^2/(4*(J:ℝ)^4) ≤ _
    have hbound : A/(2*(J:ℝ)^2) ≤ ∑e ∈ B, a e := by
      have hh := div_le_div_of_nonneg_right hRsum (sq_nonneg (J:ℝ))
      have he : (A/2)/(J:ℝ)^2 = A/(2*(J:ℝ)^2) := by ring
      change (A/2)/(J:ℝ)^2 ≤ _ at hh
      rw [he] at hh
      exact hh.trans hgain
    have hA : 0 < A := hpos
    have hnonneg : 0 ≤ A/(2*(J:ℝ)^2) := by positivity
    have hh := pow_le_pow_left₀ hnonneg hbound 2
    have he : (A/(2*(J:ℝ)^2))^2 = A^2/(4*(J:ℝ)^4) := by ring
    rw [he] at hh
    exact hh
  · intro e he
    exact lt_of_lt_of_le (by positivity : 0 < μ^2/16) (hR e (hBR he)).1

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE4} [DecidableEq E]

lemma scaled_subset (O : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hO : O.Nonempty)
    (ha : ∀e ∈ O, 0 ≤ a e) (hsq : ∀e ∈ O, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ O, a e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    {L : ℕ} (hL : Real.logb 2 (16/(α*(1/(4*((1+⌈Real.logb 2 (256/α^2)⌉₊:ℕ):ℝ)^4))))+1 < L) :
    let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
    let γ := 1/(4*(J:ℝ)^4)
    ∃B : Finset E, ∃idx : ℤ, ∃off : Fin L,
      B.Nonempty ∧ B ⊆ O ∧ γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(idx:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(idx:ℝ)) ∧
      (∀e ∈ B, 2^((idx:ℝ)+off.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((idx:ℝ)+off.val)) := by
  let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
  let γ := 1/(4*(J:ℝ)^4)
  have hJ : (0:ℝ) < J := by dsimp [J] <;> positivity
  have hγ : 0 < γ := by dsimp [γ] <;> positivity
  obtain ⟨B,hBn,hBO,hgain,hapos,hratio⟩ := homogeneous_subset O a d hα hα1 hO ha hsq hpos hbad
  obtain ⟨e₀,he₀,hmin₁⟩ := exists_min_image B (fun e => (a e)^2) hBn
  obtain ⟨f₀,hf₀,hmin₂⟩ := exists_min_image B d hBn
  let c₁ := (a e₀)^2
  let c₂ := d f₀
  have hc₁ : 0 < c₁ := hapos e₀ he₀
  have hc₁₂ : c₁ ≤ c₂ := (hmin₁ f₀ hf₀).trans (hsq f₀ (hBO hf₀))
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  have hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ B, a e)^2 := by
    simpa only [γ,one_div,inv_mul_eq_div] using hgain
  have hmax₁ : ∀e ∈ B, (a e)^2 ≤ 4*c₁ := by
    intro e he
    have hh := (hratio e he e₀ he₀).1.le
    dsimp [c₁]
    nlinarith only [hh,sq_nonneg (a e₀)]
  have hmin₂' : ∀e ∈ B, c₂/4 ≤ d e := by
    intro e he
    have hh : c₂ ≤ d e := hmin₂ e he
    linarith only [hh,hc₂]
  have hden := BagDensity.local_density O B a d hBO hBn hα hγ
    (fun e he => (sq_nonneg (a e)).trans (hsq e he)) hmax₁ hmin₂' hbad hdom
  have hcard : (B.card:ℝ) ≤ O.card := by exact_mod_cast card_le_card hBO
  have hOpos : (0:ℝ) < O.card := by exact_mod_cast card_pos.mpr hO
  have hscale : c₂ ≤ (16/(α*γ))*c₁ := by
    have hm := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 16*c₁ by positivity)
    have hh : α*γ*c₂ ≤ 16*c₁ := by
      apply (mul_le_mul_iff_right₀ hOpos).mp
      nlinarith only [hden,hm]
    calc
      c₂ ≤ 16*c₁/(α*γ) := (le_div_iff₀ (mul_pos hα hγ)).mpr (by nlinarith only [hh])
      _ = (16/(α*γ))*c₁ := by ring
  let i := ⌊Real.logb 2 c₁⌋
  let j := ⌊Real.logb 2 c₂⌋
  have hoff := ScaleSelection.integer_scale_offset hc₁ hc₁₂ hscale hL
  let o : Fin L := ⟨(j-i).toNat, by dsimp [i,j] at *; omega⟩
  have hj : ((j:ℤ):ℝ)=(i:ℝ)+(o.val:ℝ) := by
    have hh : (o.val:ℤ)=j-i := Int.toNat_of_nonneg hoff.1
    have hh' := congrArg (fun x : ℤ => (x:ℝ)) hh
    push_cast at hh'
    linarith only [hh']
  have hi := ScaleSelection.integer_dyadic hc₁
  have hj' := ScaleSelection.integer_dyadic hc₂
  refine ⟨B,i,o,hBn,hBO,hdom,?_,?_,?_,?_⟩
  · intro e he
    exact hi.1.trans (hmin₁ e he)
  · intro e he
    have hh := (hratio e he e₀ he₀).1
    have hh' : (a e)^2 < 2*c₁ := hh
    have hhi : c₁ < 2*2^(i:ℝ) := hi.2
    nlinarith only [hh',hhi]
  · intro e he
    rw [←hj]
    exact hj'.1.trans (hmin₂ e he)
  · intro e he
    rw [←hj]
    have hh := (hratio e he f₀ hf₀).2
    have hh' : d e < 2*c₂ := hh
    have hjj : c₂ < 2*2^(j:ℝ) := hj'.2
    nlinarith only [hh',hjj]
end
end StrongThinTree.Truncation

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma truncationGain_pos (α : ℝ) : 0 < truncationGain α := by
  dsimp [truncationGain,truncationBins]
  positivity

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Duality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Polar
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV2} {W : Type uW} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma sqrt_eq_real_cfc {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_cfc,cfc_nnreal_eq_real _ _ hA.nonneg]
  unfold Real.sqrt
  rfl

lemma trace_sqrt_roots {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    (CFC.sqrt A).trace=(A.charpoly.roots.map Real.sqrt).sum := by
  rw [sqrt_eq_real_cfc hA,hA.isHermitian.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self,one_mul,trace_diagonal]
  rw [hA.isHermitian.roots_charpoly_eq_eigenvalues,Multiset.map_map]
  rfl

lemma trace_sqrt_mul_comm (A : Matrix V W ℝ) (B : Matrix W V ℝ)
    (hAB : (A*B).PosSemidef) (hBA : (B*A).PosSemidef) :
    (CFC.sqrt (A*B)).trace=(CFC.sqrt (B*A)).trace := by
  rw [trace_sqrt_roots hAB,trace_sqrt_roots hBA]
  have heq := congrArg (fun p : Polynomial ℝ => (p.roots.map Real.sqrt).sum)
    (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (A*B).charpoly_monic.ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (B*A).charpoly_monic.ne_zero)] at heq
  have hz (n : ℕ) : ((n • ({0} : Multiset ℝ)).map Real.sqrt).sum=0 := by
    induction n with
    | zero => simp
    | succ n hn => simp [succ_nsmul,Multiset.map_add,hn]
  simpa [Polynomial.roots_X_pow,Multiset.map_add,hz] using heq

lemma trace_sqrt_gram (M : Matrix V W ℝ) :
    (CFC.sqrt (M*Mᵀ)).trace=(CFC.sqrt (Mᵀ*M)).trace := by
  exact trace_sqrt_mul_comm M Mᵀ
    (by simpa using posSemidef_self_mul_conjTranspose M)
    (by simpa using posSemidef_conjTranspose_mul_self M)

lemma cfc_continuousOn {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

lemma inverse_sqrt_scalar {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹*x=Real.sqrt x := by
  by_cases hx0 : x=0
  · simp [hx0]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm hx0))
    calc
      (Real.sqrt x)⁻¹*x=(Real.sqrt x)⁻¹*(Real.sqrt x*Real.sqrt x) :=
        congrArg (fun t : ℝ => (Real.sqrt x)⁻¹*t) (Real.mul_self_sqrt hx).symm
      _=Real.sqrt x := by rw [←mul_assoc,inv_mul_cancel₀ hs,one_mul]

lemma inverse_sqrt_scalar_bound {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹*x*(Real.sqrt x)⁻¹ ≤ 1 := by
  rw [inverse_sqrt_scalar hx]
  by_cases hs : Real.sqrt x=0
  · simp [hs]
  · simp [hs]

omit [DecidableEq W] in

lemma polar_optimizer (M : Matrix V W ℝ) :
    ∃ U : Matrix W V ℝ, Uᵀ*U ≤ 1 ∧
      (U*M).trace=(CFC.sqrt (M*Mᵀ)).trace := by
  let H := M*Mᵀ
  have hH : H.PosSemidef := by simpa [H] using posSemidef_self_mul_conjTranspose M
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  let P := cfc f H
  have hid : cfc (fun x : ℝ => x) H=H := cfc_id ℝ H hH.isHermitian
  have hP : P.IsHermitian := cfc_predicate f H
  have hPtrans : Pᵀ=P := isHermitian_iff_isSymm.mp hP
  have hPH : P*H=CFC.sqrt H := by
    rw [sqrt_eq_real_cfc hH]
    calc
      P*H=cfc (fun x => f x*x) H := by
        rw [cfc_mul f (fun x => x) H (cfc_continuousOn hH.isHermitian f)
          (cfc_continuousOn hH.isHermitian (fun x => x)),hid]
      _=cfc Real.sqrt H := cfc_congr (fun x hx => inverse_sqrt_scalar (spectrum_nonneg_of_nonneg hH.nonneg hx))
  have hPHP : P*H*P ≤ 1 := by
    have heq : P*H*P=cfc (fun x => f x*x*f x) H := by
      rw [cfc_mul (fun x => f x*x) f H (cfc_continuousOn hH.isHermitian _)
        (cfc_continuousOn hH.isHermitian _),cfc_mul f (fun x => x) H
        (cfc_continuousOn hH.isHermitian _) (cfc_continuousOn hH.isHermitian _),
        hid]
    rw [heq]
    exact cfc_le_one _ _ (fun x hx => inverse_sqrt_scalar_bound (spectrum_nonneg_of_nonneg hH.nonneg hx))
  refine ⟨Mᵀ*P,?_,?_⟩
  · simpa only [transpose_mul,transpose_transpose,hPtrans,Matrix.mul_assoc,H] using hPHP
  · rw [Matrix.trace_mul_cycle]
    change (M*Mᵀ*P).trace=(CFC.sqrt H).trace
    change (H*P).trace=(CFC.sqrt H).trace
    rw [Matrix.trace_mul_comm,hPH]

omit [DecidableEq W] in
lemma norm_sq_mulVec_le {U : Matrix W V ℝ} (hU : Uᵀ*U ≤ 1) (x : V → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ x) ≤ x ⬝ᵥ x := by
  have hp := (Matrix.le_iff.mp hU).dotProduct_mulVec_nonneg x
  simp only [star_trivial,sub_mulVec,one_mulVec,dotProduct_sub] at hp
  have heq : x ⬝ᵥ ((Uᵀ*U) *ᵥ x)=(U *ᵥ x) ⬝ᵥ (U *ᵥ x) := by
    rw [←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  rw [heq] at hp
  linarith only [hp]

variable {J : Type uJ2} [Fintype J] [DecidableEq J]

lemma dual_trace_rectangular (C : Matrix V W ℝ) (Y : Matrix J V ℝ) :
    (CFC.sqrt (CFC.sqrt (Yᵀ*Y)*(C*Cᵀ)*CFC.sqrt (Yᵀ*Y))).trace =
      (CFC.sqrt ((Y*C)*(Y*C)ᵀ)).trace := by
  let S := CFC.sqrt (Yᵀ*Y)
  have hZ : (Yᵀ*Y).PosSemidef := by simpa using posSemidef_conjTranspose_mul_self Y
  have hSH : Sᵀ=S := isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg (Yᵀ*Y)).posSemidef.isHermitian
  have hSS : S*S=Yᵀ*Y := CFC.sqrt_mul_sqrt_self _ hZ.nonneg
  have hleft : S*(C*Cᵀ)*S=(S*C)*(S*C)ᵀ := by
    simp only [transpose_mul,hSH,Matrix.mul_assoc]
  change (CFC.sqrt (S*(C*Cᵀ)*S)).trace=_
  rw [hleft,trace_sqrt_gram,trace_sqrt_gram (Y*C)]
  congr 2
  simp only [transpose_mul,hSH]
  calc
    (Cᵀ*S)*(S*C)=Cᵀ*(S*S)*C := by simp only [Matrix.mul_assoc]
    _=(Cᵀ*Yᵀ)*(Y*C) := by rw [hSS]; simp only [Matrix.mul_assoc]

lemma signed_diag_orthogonal (a : W → ℝ) :
    let D : Matrix W W ℝ := diagonal (fun e => if 0 ≤ a e then (1:ℝ) else -1)
    Dᵀ*D=1 := by
  dsimp
  rw [diagonal_transpose,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [diagonal_apply_eq,one_apply_eq]
    split_ifs <;> norm_num
  · simp [diagonal_apply_ne _ hij,one_apply_ne hij]

lemma positive_optimizer (M : Matrix V W ℝ) (w : W → ℝ) (hw : ∀e, 0 ≤ w e) :
    ∃ U : Matrix W V ℝ, Uᵀ*U ≤ 1 ∧ (∀e, 0 ≤ (U*M) e e) ∧
      (CFC.sqrt ((M*diagonal w)*(M*diagonal w)ᵀ)).trace ≤
        ∑e, w e*(U*M) e e := by
  obtain ⟨U,hU,htr⟩ := polar_optimizer (M*diagonal w)
  let a : W → ℝ := fun e => (U*M) e e
  let s : W → ℝ := fun e => if 0 ≤ a e then 1 else -1
  let D : Matrix W W ℝ := diagonal s
  have hDD : Dᵀ*D=1 := signed_diag_orthogonal a
  have hsa (e : W) : s e*a e=|a e| := by
    dsimp [s]
    split_ifs with he
    · simp [abs_of_nonneg he]
    · simp [abs_of_neg (lt_of_not_ge he)]
  have hdiag (e : W) : ((D*U)*M) e e=|a e| := by
    rw [Matrix.mul_assoc]
    change (diagonal s*(U*M)) e e=|a e|
    rw [diagonal_mul]
    exact hsa e
  refine ⟨D*U,?_,fun e => (hdiag e).symm ▸ abs_nonneg _,?_⟩
  · have heq : (D*U)ᵀ*(D*U)=Uᵀ*U := by
      rw [transpose_mul]
      calc
        (Uᵀ*Dᵀ)*(D*U)=Uᵀ*(Dᵀ*D)*U := by simp only [Matrix.mul_assoc]
        _=Uᵀ*U := by rw [hDD,Matrix.mul_one]
    rw [heq]
    exact hU
  · rw [←htr,←Matrix.mul_assoc]
    unfold Matrix.trace
    apply sum_le_sum
    intro e _
    change (U*M*diagonal w) e e ≤ w e*((D*U)*M) e e
    rw [mul_diagonal,hdiag]
    change a e*w e ≤ w e*|a e|
    rw [mul_comm (a e)]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (hw e)
end
end StrongThinTree.Polar

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma trace_outer_mul (v : V → ℝ) (D : Matrix V V ℝ) :
    (vecMulVec v v * D).trace = v ⬝ᵥ (D *ᵥ v) := by
  rw [vecMulVec_mul,trace_vecMulVec,dotProduct_comm,dotProduct_mulVec]

lemma weighted_rows_bound (O : T → Finset E) (lam : T → ℝ) (a : E → ℝ)
    (hlam : ∀t, 0 ≤ lam t) (hsum : (∑t, lam t)=1) (ha : ∀e, 0 ≤ a e) :
    (∑e, Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0)*a e)^2 ≤
      ∑t, (∑e ∈ O t, a e)^2/((O t).card : ℝ) := by
  let r : T → ℝ := fun t => Real.sqrt (lam t / ((O t).card : ℝ))
  let c : T → ℝ := fun t => (∑e ∈ O t, a e)/Real.sqrt ((O t).card : ℝ)
  have hw (e : E) : Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) ≤
      ∑t, if e ∈ O t then r t else 0 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨sum_nonneg (fun t _ => by split_ifs; exact Real.sqrt_nonneg _; exact le_rfl), ?_⟩
    calc
      (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) =
          ∑t, (if e ∈ O t then r t else 0)^2 := by
        apply sum_congr rfl
        intro t _
        split_ifs
        · exact (Real.sq_sqrt (div_nonneg (hlam t) (Nat.cast_nonneg _))).symm
        · norm_num
      _ ≤ _ := sum_sq_le_sq_sum_of_nonneg (fun t _ => by split_ifs; exact Real.sqrt_nonneg _; exact le_rfl)
  have heq : (∑e, (∑t, if e ∈ O t then r t else 0)*a e) =
      ∑t, Real.sqrt (lam t)*c t := by
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    calc
      (∑e, (if e ∈ O t then r t else 0)*a e) = r t*∑e ∈ O t, a e := by
        rw [mul_sum]
        simp only [ite_mul,zero_mul]
        rw [←sum_filter]
        simp
      _ = Real.sqrt (lam t)*c t := by
        dsimp [r,c]
        rw [Real.sqrt_div (hlam t)]
        ring
  have hle := sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) =>
    mul_le_mul_of_nonneg_right (hw e) (ha e))
  rw [heq] at hle
  have hsq := pow_le_pow_left₀ (sum_nonneg (fun e _ =>
    mul_nonneg (Real.sqrt_nonneg _) (ha e))) hle 2
  have hc := sum_mul_sq_le_sq_mul_sq univ (fun t => Real.sqrt (lam t)) c
  have hs : (∑t, (Real.sqrt (lam t))^2)=1 := by simpa only [Real.sq_sqrt (hlam _)] using hsum
  rw [hs,one_mul] at hc
  refine hsq.trans (hc.trans_eq ?_)
  apply sum_congr rfl
  intro t _
  simp only [c,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

omit [Fintype V] [DecidableEq V] in
lemma objectiveMatrix_eq_sum_edges (b : E → V → ℝ) (O : T → Finset E) (lam : T → ℝ) :
    objectiveMatrix b O lam = ∑e, (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) •
      vecMulVec (b e) (b e) := by
  have ht (t : T) : lam t • boundaryMatrix b O t =
      ∑e, (if e ∈ O t then lam t / ((O t).card : ℝ) else 0) • vecMulVec (b e) (b e) := by
    simp only [boundaryMatrix,smul_smul,div_eq_mul_inv,smul_sum,ite_smul,zero_smul]
    rw [←sum_filter]
    simp
  simp only [objectiveMatrix,ht]
  rw [sum_comm]
  simp only [sum_smul]

omit [Fintype V] [DecidableEq V] in
lemma weighted_gram (b : E → V → ℝ) (w : E → ℝ) :
    let B : Matrix V E ℝ := fun v e => b e v
    (B*diagonal w)*(B*diagonal w)ᵀ=∑e, (w e)^2 • vecMulVec (b e) (b e) := by
  dsimp
  ext i j
  change (∑e, ((Matrix.of (fun v e => b e v))*diagonal w) i e *
    ((Matrix.of (fun v e => b e v))*diagonal w) j e) = _
  simp only [mul_diagonal,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,Matrix.of_apply]
  apply sum_congr rfl
  intro e _
  ring

omit [Fintype V] [DecidableEq V] in
lemma objectiveMatrix_gram (b : E → V → ℝ) (O : T → Finset E) {lam : T → ℝ}
    (hlam : ∀t, 0 ≤ lam t) :
    let C : Matrix V E ℝ := (Matrix.of (fun v e => b e v))*diagonal (edgeWeight O lam)
    objectiveMatrix b O lam=C*Cᵀ := by
  dsimp
  rw [weighted_gram,objectiveMatrix_eq_sum_edges]
  apply sum_congr rfl
  intro e _
  have hp : 0 ≤ ∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0 :=
    sum_nonneg (fun t _ => by split_ifs; exact div_nonneg (hlam t) (Nat.cast_nonneg _); exact le_rfl)
  rw [edgeWeight,Real.sq_sqrt hp]
  rfl

lemma nuclear_bound_of_embedding_bound (b : E → V → ℝ) (O : T → Finset E)
    {H : Type uH} [Fintype H] [DecidableEq H] (X : Matrix H V ℝ) {K : ℝ}
    (hbound : ∀U : Matrix E H ℝ, Uᵀ*U ≤ 1 → (∀e, 0 ≤ (U*(X*(Matrix.of (fun v e => b e v)))) e e) →
      (∑t, (∑e ∈ O t, (U*(X*(Matrix.of (fun v e => b e v)))) e e)^2/((O t).card : ℝ)) ≤ K)
    {lam : T → ℝ} (hlam : ∀t, 0 ≤ lam t) (hsum : (∑t, lam t)=1) :
    (CFC.sqrt (CFC.sqrt (Xᵀ*X)*objectiveMatrix b O lam*CFC.sqrt (Xᵀ*X))).trace^2 ≤ K := by
  let B : Matrix V E ℝ := fun v e => b e v
  let w := edgeWeight O lam
  have hw : ∀e, 0 ≤ w e := fun e => Real.sqrt_nonneg _
  obtain ⟨U,hU,hpos,htr⟩ := Polar.positive_optimizer (X*B) w hw
  rw [objectiveMatrix_gram b O hlam,Polar.dual_trace_rectangular]
  change (CFC.sqrt ((X*(B*diagonal w))*(X*(B*diagonal w))ᵀ)).trace^2 ≤ K
  rw [←Matrix.mul_assoc]
  have hsq := pow_le_pow_left₀ (CFC.sqrt_nonneg _).posSemidef.trace_nonneg htr 2
  exact hsq.trans ((weighted_rows_bound O lam (fun e => (U*(X*B)) e e) hlam hsum hpos).trans
    (hbound U hU hpos))

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

lemma contraction_edge_diag (X : Matrix (Fin h) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin h) ℝ) (e : Fin m) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    (Y (G.left e)-Y (G.right e)).ofLp e =
      (U*(X*Matrix.of (fun v e => G.incidence e v))) e e := by
  change (∑i, U e i*X i (G.left e))-(∑i, U e i*X i (G.right e)) = _
  change (∑i, U e i*X i (G.left e))-(∑i, U e i*X i (G.right e)) =
    ∑i, U e i*(∑v, X i v*G.incidence e v)
  simp_rw [G.eval_incidence,mul_sub]
  rw [sum_sub_distrib]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Filter
open scoped Topology
namespace StrongThinTree.ShortcutNumeric
open MultiGraph.Hierarchy

lemma count_pos {x : ℝ} (hx : 0 < x) : 0 < count x :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx _)

end StrongThinTree.ShortcutNumeric

namespace StrongThinTree.MultiGraph.Hierarchy
open Matrix Finset ShortcutNumeric
open scoped Classical MatrixOrder
variable {n m : ℕ} {G : MultiGraph n m} {H : Hierarchy n}

lemma edgeConnected_of_locally {q : ℕ} (hconn : H.LocallyConnectedReal G q) : G.EdgeConnected q := by
  intro S hS hS'
  have hh := hconn univ H.root_mem S hS (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩)
  have heq : G.inducedEdges univ=univ := by ext e; simp [MultiGraph.inducedEdges]
  rw [heq] at hh
  exact_mod_cast hh

end StrongThinTree.MultiGraph.Hierarchy

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Profiles
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric profiles. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set

section Profiles

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

omit [Fintype V] in
lemma profile_mem (x : V) : profile x ∈ polytope :=
  subset_convexHull ℝ _ (Set.mem_range_self x)

omit [Fintype V] in
lemma polytope_convex : Convex ℝ (polytope (V := V)) := convex_convexHull ℝ _

lemma profile_norm_sub (x y : V) : ‖profile x - profile y‖ = dist x y := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg dist_nonneg).2
    intro z
    simp only [Pi.sub_apply, profile, Real.norm_eq_abs]
    apply abs_sub_le_iff.2
    constructor
    · linarith [dist_triangle x y z]
    · have h := dist_triangle y x z
      rw [dist_comm y x] at h
      linarith
  · have h := norm_le_pi_norm (profile x - profile y) y
    simpa [profile, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h

omit [PseudoMetricSpace V] in
lemma norm_coordinate_convex (c : V → ℝ) (i : V) :
    Convex ℝ {x : V → ℝ | ‖x - c‖ ≤ x i} := by
  intro x hx y hy a b ha hb hab
  change ‖a • x + b • y - c‖ ≤ (a • x + b • y) i
  have heq : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination c j * hab
  rw [heq]
  calc
    ‖a • (x - c) + b • (y - c)‖ ≤ ‖a • (x - c)‖ + ‖b • (y - c)‖ := norm_add_le _ _
    _ = a * ‖x - c‖ + b * ‖y - c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * x i + b * y i := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = (a • x + b • y) i := rfl

theorem radius_eq_coordinate {q : V → ℝ} (hq : q ∈ polytope) (x : V) :
    ‖q - profile x‖ = q x := by
  have hupper : ‖q - profile x‖ ≤ q x := by
    apply convexHull_min (t := {y : V → ℝ | ‖y - profile x‖ ≤ y x}) ?_
      (norm_coordinate_convex (profile x) x) hq
    rintro _ ⟨y, rfl⟩
    exact (profile_norm_sub y x).le
  have hlower : q x ≤ ‖q - profile x‖ := by
    have h := norm_le_pi_norm (q - profile x) x
    simp only [Pi.sub_apply, profile, dist_self, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  exact le_antisymm hupper hlower

end Profiles

section Double

variable (V : Type*) [Fintype V] [PseudoMetricSpace V]

variable {V}

lemma dist_plus (x y : V) : dist (plus x) (plus y) = dist x y := by
  change doubledDist _ _ = _
  simp [doubledDist, plus]

end Double

section RadialMotion

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

lemma mix_mem {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : mix q r t ∈ polytope :=
  polytope_convex hq hr (sub_nonneg.mpr ht.2) ht.1 (by ring)

lemma radius_mix {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q r t - profile x‖ = (1 - t) * ‖q - profile x‖ + t * ‖r - profile x‖ := by
  rw [radius_eq_coordinate (mix_mem hq hr ht), radius_eq_coordinate hq,
    radius_eq_coordinate hr]
  rfl

end RadialMotion

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ShellCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric shell charging. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set StrongThinTree.Geometry

variable {V I : Type*} [Fintype V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma radius_reverse_triangle (q r c : V → ℝ) :
    |‖r - c‖ - ‖q - c‖| ≤ ‖r - q‖ := by
  have h := abs_norm_sub_norm_le (r - c) (q - c)
  simpa only [sub_sub_sub_cancel_right] using h

theorem shell_segment_length_bound [Fintype I] (c : I → V) (a b : I → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hdis : Pairwise (fun i j => Disjoint
      (relativeShell (profile (c i)) (a i) (b i))
      (relativeShell (profile (c j)) (a j) (b j))))
    {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope) :
    ∑ i, |clamp (a i) (b i) ‖q - profile (c i)‖ -
      clamp (a i) (b i) ‖r - profile (c i)‖| ≤ ‖r - q‖ := by
  apply clamped_affine_disjoint_sum a b
    (fun i => ‖q - profile (c i)‖) (fun i => ‖r - profile (c i)‖)
    (norm_nonneg _) hab (fun i => radius_reverse_triangle q r (profile (c i)))
  rintro i j hij t ht ⟨hia, hib, hja, hjb⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrad (s : V) : ‖mix q r t - profile s‖ =
      ‖q - profile s‖ + t * (‖r - profile s‖ - ‖q - profile s‖) := by
    rw [radius_mix hq hr s ht']
    ring
  apply Set.disjoint_left.mp (hdis hij) (mix_mem hq hr ht' |> fun hm =>
    show mix q r t ∈ relativeShell (profile (c i)) (a i) (b i) from
      ⟨hm, by rwa [hrad], by rwa [hrad]⟩)
  exact ⟨mix_mem hq hr ht', by rwa [hrad], by rwa [hrad]⟩

theorem shell_length_bound {n m k : ℕ} (G : StrongThinTree.MultiGraph n m)
    (hk : G.EdgeConnected k) (X : Fin n → V) [Fintype I]
    (c : I → V) (a b : I → ℝ) (hab : ∀ i, a i ≤ b i)
    (hinner : ∀ i, ∃ u, dist (X u) (c i) ≤ a i)
    (houter : ∀ i, ∃ v, b i ≤ dist (X v) (c i))
    (hdis : Pairwise (fun i j => Disjoint
      (relativeShell (profile (c i)) (a i) (b i))
      (relativeShell (profile (c j)) (a j) (b j)))) :
    (k : ℝ) * ∑ i, (b i - a i) ≤
      ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
  calc
    _ = ∑ i, (k : ℝ) * (b i - a i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ∑ e : Fin m,
        |clamp (a i) (b i) (dist (X (G.left e)) (c i)) -
          clamp (a i) (b i) (dist (X (G.right e)) (c i))| := by
      exact Finset.sum_le_sum fun i _ => G.clamped_variation_lower hk
        (fun u => dist (X u) (c i)) (hab i) (hinner i) (houter i)
    _ = ∑ e : Fin m, ∑ i,
        |clamp (a i) (b i) (dist (X (G.left e)) (c i)) -
          clamp (a i) (b i) (dist (X (G.right e)) (c i))| := Finset.sum_comm
    _ ≤ ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
      apply Finset.sum_le_sum
      intro e _
      have h := shell_segment_length_bound c a b hab hdis
        (profile_mem (X (G.left e))) (profile_mem (X (G.right e)))
      simpa only [profile_norm_sub, dist_comm (X (G.right e)) (X (G.left e))] using h

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CompactCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compact charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset

section RadialLaws
variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_self (q : J → ℝ) : normDistance q q = 0 := by
  simp [normDistance]

omit [PseudoMetricSpace J] in
lemma normDistance_triangle (q r s : J → ℝ) :
    normDistance q s ≤ normDistance q r + normDistance r s := by
  simpa only [normDistance, dist_eq_norm] using dist_triangle q r s

omit [Fintype J] in
lemma isProfile_inPolytope {q : J → ℝ} (hq : isProfile q) : inPolytope q := by
  obtain ⟨j,rfl⟩ := hq
  exact profile_mem j

omit [PseudoMetricSpace J] in
lemma segment_formula (q r : J → ℝ) (t : ℝ) :
    (fun j => q j+t*(r j-q j)) = mix q r t := by
  ext j
  simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma inPolytope_segment {q r : J → ℝ} (hq : inPolytope q) (hr : inPolytope r)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    inPolytope (fun j => q j+t*(r j-q j)) := by
  rw [segment_formula]
  exact mix_mem hq hr ht

lemma isProfile_radial_affine {q r c : J → ℝ} (hq : inPolytope q) (hr : inPolytope r)
    (hc : isProfile c) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    normDistance (fun j => q j+t*(r j-q j)) c =
      normDistance q c+t*(normDistance r c-normDistance q c) := by
  obtain ⟨j,rfl⟩ := hc
  rw [segment_formula]
  change ‖mix q r t-profile j‖ = _
  rw [radius_mix hq hr j ht]
  unfold normDistance
  ring
end RadialLaws

namespace RadialShell
variable {V : Type*} {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma valid_width_pos {X : V → J → ℝ} {H : RadialShell V} (hH : H.Valid X) :
    0 < H.width := sub_pos.mpr hH.2.1

lemma support_ball (X : V → J → ℝ) (v : V) (r : ℝ) :
    (ball v r).support X = {w | inPolytope w ∧ normDistance w (X v) < r} := by
  ext w
  simp [support,ball]

lemma support_hollow (X : V → J → ℝ) (v : V) (a b : ℝ) :
    (hollow v a b).support X = {w | inPolytope w ∧ a<normDistance w (X v) ∧ normDistance w (X v)<b} := by
  ext w
  simp only [support,hollow,Set.mem_ofPred_eq,Bool.false_eq_true,false_or]
  tauto

lemma valid_support_nonempty {X : V → J → ℝ} (hX : ∀v, isProfile (X v))
    {H : RadialShell V} (hH : H.Valid X) : (H.support X).Nonempty := by
  obtain ⟨v,hv⟩ := hH.2.2.2.2
  let R := normDistance (X v) (X H.center)
  let q := (H.inner+H.outer)/2
  have hq : H.inner<q ∧ q<H.outer := by dsimp [q]; constructor <;> linarith [hH.2.1]
  have hR : 0 < R := lt_of_lt_of_le (lt_of_le_of_lt hH.1 hH.2.1) hv
  let t := q/R
  have ht : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (le_trans hH.1 hq.1.le) hR.le,
      (div_le_one hR).mpr (le_trans hq.2.le hv)⟩
  let w := fun j => X H.center j+t*(X v j-X H.center j)
  have hw : normDistance w (X H.center) = q := by
    rw [isProfile_radial_affine (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _)) (hX _) ht,
      normDistance_self, sub_zero, zero_add]
    exact div_mul_cancel₀ _ hR.ne'
  exact ⟨w,inPolytope_segment (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _)) ht,
    hw ▸ hq.2,Or.inr (hw ▸ hq.1)⟩

omit [PseudoMetricSpace J] in
lemma restriction_valid {X : V → J → ℝ} {H : RadialShell V}
    (hH : H.Valid X) {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) (hab : a < b) :
    (hollow H.center a b).Valid X := by
  refine ⟨hH.1.trans ha,hab,by simp [hollow],?_,?_⟩
  · obtain ⟨u,hu⟩ := hH.2.2.2.1
    exact ⟨u,hu.trans ha⟩
  · obtain ⟨v,hv⟩ := hH.2.2.2.2
    exact ⟨v,hb.trans hv⟩

lemma restriction_subset (X : V → J → ℝ) (H : RadialShell V)
    {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) :
    (hollow H.center a b).support X ⊆ H.support X := by
  intro w hw
  rw [support_hollow] at hw
  exact ⟨hw.1,lt_of_lt_of_le hw.2.2 hb,Or.inr (lt_of_le_of_lt ha hw.2.1)⟩

lemma ball_subset_of_radial_margin (X : V → J → ℝ) (H : RadialShell V)
    (z : V) {δ : ℝ} (hlo : H.inner+δ ≤ normDistance (X z) (X H.center))
    (hhi : normDistance (X z) (X H.center) ≤ H.outer-δ) :
    (ball z δ).support X ⊆ H.support X := by
  intro w hw
  rw [support_ball] at hw
  have htri := normDistance_triangle w (X z) (X H.center)
  have htri' := normDistance_triangle (X z) w (X H.center)
  rw [normDistance_comm (X z) w] at htri'
  exact ⟨hw.1,by linarith [hw.2],Or.inr (by linarith [hw.2])⟩

lemma ball_disjoint_hollow_lower (X : V → J → ℝ) (x z : V) {δ q a : ℝ}
    (hq : q+δ ≤ normDistance (X z) (X x)) :
    Disjoint ((ball z δ).support X) ((hollow x a q).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := normDistance_triangle (X z) w (X x)
  rw [normDistance_comm (X z) w] at ht
  linarith [hw.2,hz.2.2]

lemma ball_disjoint_hollow_upper (X : V → J → ℝ) (x z : V) {δ q b : ℝ}
    (hq : normDistance (X z) (X x)+δ ≤ q) :
    Disjoint ((ball z δ).support X) ((hollow x q b).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := normDistance_triangle w (X z) (X x)
  linarith [hw.2,hz.2.1]

lemma concentric_disjoint (X : V → J → ℝ) (x : V) {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint ((hollow x a b).support X) ((hollow x c d).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_hollow] at hw hz
  linarith [hw.2.2,hz.2.1]

lemma disjoint_balls_distance {X : V → J → ℝ} (hX : ∀v, isProfile (X v))
    (u v : V) {δ : ℝ} (hd : Disjoint ((ball u δ).support X) ((ball v δ).support X)) :
    2*δ ≤ normDistance (X u) (X v) := by
  by_contra hh
  have hh := not_le.mp hh
  let w := fun j => X u j+(1/2:ℝ)*(X v j-X u j)
  have hw := inPolytope_segment (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v))
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hu := isProfile_radial_affine (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v)) (hX u)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hv := isProfile_radial_affine (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v)) (hX v)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  simp only [normDistance_self,normDistance_comm (X v) (X u)] at hu hv
  have hwu : w ∈ (ball u δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w] <;> linarith⟩
  have hwv : w ∈ (ball v δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w] <;> linarith⟩
  exact Set.disjoint_left.mp hd hwu hwv

end RadialShell
end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

omit [DecidableEq V] in
lemma arrangement_empty : Arrangement X ∅ := by simp [Arrangement]

omit [DecidableEq V] in
lemma arrangement_subset {O P : Finset (RadialShell V)} (hO : Arrangement X O) (hPO : P ⊆ O) :
    Arrangement X P := ⟨fun H hH => hO.1 H (hPO hH),hO.2.mono hPO⟩

omit [DecidableEq V] in
lemma arrangement_disjoint_finsets (hX : ∀v, isProfile (X v))
    {O P : Finset (RadialShell V)} (hO : Arrangement X O)
    (hd : ∀H ∈ O, ∀K ∈ P, Disjoint (H.support X) (K.support X)) : Disjoint O P := by
  rw [Finset.disjoint_left]
  intro H hHO hHP
  obtain ⟨w,hw⟩ := valid_support_nonempty hX (hO.1 H hHO)
  exact Set.disjoint_left.mp (hd H hHO H hHP) hw hw

lemma arrangement_union {O P : Finset (RadialShell V)}
    (hO : Arrangement X O) (hP : Arrangement X P)
    (hd : ∀H ∈ O, ∀K ∈ P, Disjoint (H.support X) (K.support X)) : Arrangement X (O ∪ P) := by
  constructor
  · intro H hH
    rcases mem_union.mp hH with hH | hH
    · exact hO.1 H hH
    · exact hP.1 H hH
  · intro H hH K hK hne
    rcases mem_union.mp hH with hH | hH <;> rcases mem_union.mp hK with hK | hK
    · exact hO.2 hH hK hne
    · exact hd H hH K hK
    · exact (hd K hK H hH).symm
    · exact hP.2 hH hK hne

lemma image_restriction_injective (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) :
    Set.InjOn f (O : Set (RadialShell V)) := by
  intro H hH K hK heq
  by_contra hne
  obtain ⟨w,hw⟩ := valid_support_nonempty hX (hf H hH).1
  exact Set.disjoint_left.mp (hO.2 hH hK hne) ((hf H hH).2 hw)
    ((hf K hK).2 (heq ▸ hw))

lemma arrangement_image_restriction {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) :
    Arrangement X (O.image f) := by
  constructor
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := mem_image.mp hH
    exact (hf K hK).1
  · intro H hH K hK hne
    obtain ⟨H',hH',rfl⟩ := mem_image.mp hH
    obtain ⟨K',hK',rfl⟩ := mem_image.mp hK
    exact (hO.2 hH' hK' (by intro heq; exact hne (congrArg f heq))).mono
      (hf H' hH').2 (hf K' hK').2

omit [DecidableEq V] in
lemma capacity_nonneg (Δ : ℝ) (H : RadialShell V) : 0 ≤ capacity Δ H := le_max_right _ _
omit [DecidableEq V] in
lemma capacity_ge_formal (Δ : ℝ) (H : RadialShell V) : H.width-6*Δ ≤ capacity Δ H := le_max_left _ _

lemma potential_union {O P : Finset (RadialShell V)} (hOP : Disjoint O P) (Δ : ℝ) :
    potential Δ (O ∪ P) = potential Δ O+potential Δ P := sum_union hOP

lemma potential_erase {O : Finset (RadialShell V)} {H : RadialShell V}
    (hH : H ∈ O) (Δ : ℝ) : potential Δ (O.erase H)+capacity Δ H = potential Δ O :=
  sum_erase_add _ _ hH

lemma potential_image_restriction (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) (Δ : ℝ) :
    potential Δ (O.image f) = ∑H ∈ O, capacity Δ (f H) := by
  exact sum_image (fun H hH K hK heq => image_restriction_injective hX hO f hf hH hK heq)

omit [DecidableEq V] in
lemma capacity_ball {δ Δ : ℝ} (h : 6*Δ ≤ δ) (v : V) :
    capacity Δ (ball v δ) = δ-6*Δ := by
  simp only [capacity,width,ball,sub_zero]
  exact max_eq_left (sub_nonneg.mpr h)

omit [DecidableEq V] in
lemma ball_injective (δ : ℝ) : Function.Injective (fun v : V => ball v δ) := by
  intro u v heq
  exact congrArg RadialShell.center heq

lemma potential_balls {δ Δ : ℝ} (h : 6*Δ ≤ δ) (C : Finset V) :
    potential Δ (C.image (fun v => ball v δ)) = (C.card : ℝ)*(δ-6*Δ) := by
  rw [potential,sum_image (fun _ _ _ _ heq => ball_injective δ heq)]
  simp only [capacity_ball h,sum_const,nsmul_eq_mul]

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

omit [DecidableEq V] in
lemma potential_filter_width (O : Finset (RadialShell V)) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    potential Δ (O.filter (fun H => 0 < H.width)) = potential Δ O := by
  apply sum_subset (filter_subset _ _)
  intro H hH hn
  have hw : H.width ≤ 0 := le_of_not_gt (fun hh => hn (mem_filter.mpr ⟨hH,hh⟩))
  exact max_eq_right (by nlinarith)

lemma arrangement_balls {U : Finset V} {δ : ℝ}
    (hv : ∀u ∈ U, (ball u δ).Valid X)
    (hd : (U : Set V).Pairwise (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X))) :
    Arrangement X (U.image (fun v => ball v δ)) := by
  constructor
  · intro H hH
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hH
    exact hv u hu
  · intro H hH K hK hne
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hH
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hK
    exact hd hu hv (by intro heq; exact hne (congrArg (fun z => ball z δ) heq))

lemma split_shells (_hX : ∀v, isProfile (X v))
    {H : RadialShell V} (hH : H.Valid X) {L R δ Δ Δ' n : ℝ}
    (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (_hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2)
    (hL : H.inner+δ ≤ L) (hR : R ≤ H.outer-δ) (hLR : L ≤ R)
    (hspan : R-L ≤ Δ) (hn : 36*Δ ≤ n*δ) :
    ∃P : Finset (RadialShell V), Arrangement X P ∧
      (∀K ∈ P, K.support X ⊆ H.support X) ∧
      (∀z, L ≤ normDistance (X z) (X H.center) → normDistance (X z) (X H.center) ≤ R →
        ∀K ∈ P, Disjoint ((ball z δ).support X) (K.support X)) ∧
      capacity Δ H+n*δ/4 ≤ potential Δ P+n*(δ-6*Δ') := by
  let A := hollow H.center H.inner (L-δ)
  let B := hollow H.center (R+δ) H.outer
  let P := ({A,B} : Finset (RadialShell V)).filter (fun K => 0 < K.width)
  have hΔ0 : 0 ≤ Δ := by linarith
  have hA : H.inner ≤ L-δ := by linarith
  have hB : R+δ ≤ H.outer := by linarith
  have hAB : A ≠ B := by
    intro heq
    have := congrArg RadialShell.inner heq
    change H.inner = R+δ at this
    linarith
  have hpA : L-δ ≤ H.outer := by linarith
  have hpB : H.inner ≤ R+δ := by linarith
  have hdAB : Disjoint (A.support X) (B.support X) := concentric_disjoint X H.center (by linarith)
  have hv : ∀K ∈ P, K.Valid X := by
    intro K hK
    obtain ⟨hK,hw⟩ := mem_filter.mp hK
    rcases mem_insert.mp hK with rfl | hK
    · exact restriction_valid hH le_rfl hpA (by exact sub_pos.mp hw)
    · have heq := mem_singleton.mp hK
      subst K
      exact restriction_valid hH hpB le_rfl (by exact sub_pos.mp hw)
  have hsub : ∀K ∈ P, K.support X ⊆ H.support X := by
    intro K hK
    have hK := (mem_filter.mp hK).1
    rcases mem_insert.mp hK with rfl | hK
    · exact restriction_subset X H le_rfl hpA
    · have heq := mem_singleton.mp hK
      subst K
      exact restriction_subset X H hpB le_rfl
  have harr : Arrangement X P := by
    refine ⟨hv,?_⟩
    intro J hJ K hK hne
    have hJ := (mem_filter.mp hJ).1
    have hK := (mem_filter.mp hK).1
    simp only [mem_insert,mem_singleton] at hJ hK
    rcases hJ with rfl | rfl <;> rcases hK with rfl | rfl
    · exact (hne rfl).elim
    · exact hdAB
    · exact hdAB.symm
    · exact (hne rfl).elim
  refine ⟨P,harr,hsub,?_,?_⟩
  · intro z hzL hzR K hK
    have hK := (mem_filter.mp hK).1
    rcases mem_insert.mp hK with rfl | hK
    · exact ball_disjoint_hollow_lower X H.center z (by linarith)
    · have heq := mem_singleton.mp hK
      subst K
      exact ball_disjoint_hollow_upper X H.center z (by linarith)
  · have hp : potential Δ P = capacity Δ A+capacity Δ B := by
      rw [show P = ({A,B} : Finset (RadialShell V)).filter (fun K => 0 < K.width) from rfl,
        potential_filter_width _ hΔ0]
      simp [potential,hAB]
    rw [hp]
    have hn0 : 0 ≤ n := by nlinarith
    have hnew : n*δ/2 ≤ n*(δ-6*Δ') := by nlinarith
    have hcapA := capacity_ge_formal Δ A
    have hcapB := capacity_ge_formal Δ B
    have hcapA0 := capacity_nonneg Δ A
    have hcapB0 := capacity_nonneg Δ B
    change L-δ-H.inner-6*Δ ≤ capacity Δ A at hcapA
    change H.outer-(R+δ)-6*Δ ≤ capacity Δ B at hcapB
    by_cases ht : H.width-6*Δ ≤ 0
    · rw [capacity,max_eq_right ht]
      nlinarith
    · rw [capacity,max_eq_left (le_of_not_ge ht)]
      dsimp [width]
      nlinarith

lemma shrink_shells (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    {δ Δ Δ' : ℝ} (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (_hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2) :
    ∃P : Finset (RadialShell V), Arrangement X P ∧
      (∀K ∈ P, ∃H ∈ O, K.support X ⊆ H.support X) ∧
      (∀z, (∀H ∈ O, ¬(H.inner+δ+Δ ≤ normDistance (X z) (X H.center) ∧
        normDistance (X z) (X H.center) ≤ H.outer-δ-Δ)) →
        ∀K ∈ P, Disjoint ((ball z δ).support X) (K.support X)) ∧
      potential Δ O ≤ potential Δ' P := by
  let s := 2*δ+Δ
  let f := fun H : RadialShell V => hollow H.center (H.inner+s) (H.outer-s)
  let Q := O.filter (fun H => 2*s < H.width)
  have hs : 0 ≤ s := by dsimp [s] <;> linarith
  have hres : 2*s+6*Δ' ≤ 6*Δ := by dsimp [s] <;> linarith
  have hQ : Arrangement X Q := arrangement_subset hO (filter_subset _ _)
  have hf : ∀H ∈ Q, (f H).Valid X ∧ (f H).support X ⊆ H.support X := by
    intro H hH
    obtain ⟨hH,hw⟩ := mem_filter.mp hH
    exact ⟨restriction_valid (hO.1 H hH) (by linarith) (by linarith)
      (by dsimp [width] at hw <;> linarith),restriction_subset X H (by linarith) (by linarith)⟩
  refine ⟨Q.image f,arrangement_image_restriction hQ f hf,?_,?_,?_⟩
  · intro K hK
    obtain ⟨H,hH,rfl⟩ := mem_image.mp hK
    exact ⟨H,(mem_filter.mp hH).1,(hf H hH).2⟩
  · intro z hz K hK
    obtain ⟨H,hH,rfl⟩ := mem_image.mp hK
    have hz := hz H (mem_filter.mp hH).1
    by_cases hlo : H.inner+δ+Δ ≤ normDistance (X z) (X H.center)
    · have hhi : H.outer-δ-Δ < normDistance (X z) (X H.center) :=
        lt_of_not_ge (fun hh => hz ⟨hlo,hh⟩)
      exact ball_disjoint_hollow_lower X H.center z (by dsimp [s] <;> linarith)
    · have hlo := lt_of_not_ge hlo
      exact ball_disjoint_hollow_upper X H.center z (by dsimp [s] <;> linarith)
  · rw [potential_image_restriction hX hQ f hf]
    have heq : potential Δ O = potential Δ Q := by
      symm
      apply sum_subset (filter_subset _ _)
      intro H hH hn
      have hw : H.width ≤ 2*s := le_of_not_gt (fun hh => hn (mem_filter.mpr ⟨hH,hh⟩))
      exact max_eq_right (by linarith)
    rw [heq]
    apply sum_le_sum
    intro H hH
    apply max_le_max_right
    dsimp [f,width,hollow]
    linarith

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

omit [DecidableEq V] [PseudoMetricSpace J] in
lemma radial_span {D : Finset V} (hD : D.Nonempty) {Δ δ : ℝ}
    (hdiam : ∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ)
    {H : RadialShell V} {z : V} (hz : z ∈ D)
    (hint : H.inner+δ+Δ ≤ normDistance (X z) (X H.center) ∧
      normDistance (X z) (X H.center) ≤ H.outer-δ-Δ) :
    ∃L R : ℝ, H.inner+δ ≤ L ∧ R ≤ H.outer-δ ∧ L ≤ R ∧ R-L ≤ Δ ∧
      (∀u ∈ D, L ≤ normDistance (X u) (X H.center) ∧ normDistance (X u) (X H.center) ≤ R) := by
  obtain ⟨u,hu,humin⟩ := D.exists_min_image (fun v => normDistance (X v) (X H.center)) hD
  obtain ⟨v,hv,hvmax⟩ := D.exists_max_image (fun v => normDistance (X v) (X H.center)) hD
  refine ⟨normDistance (X u) (X H.center),normDistance (X v) (X H.center),?_,?_,?_,?_,?_⟩
  · have ht := normDistance_triangle (X z) (X u) (X H.center)
    have hd := hdiam z hz u hu
    linarith [hint.1]
  · have ht := normDistance_triangle (X v) (X z) (X H.center)
    have hd := hdiam v hv z hz
    linarith [hint.2]
  · exact humin v hv
  · have ht := normDistance_triangle (X v) (X u) (X H.center)
    linarith [hdiam v hv u hu]
  · exact fun w hw => ⟨humin w hw,hvmax w hw⟩

lemma compact_phase (hX : ∀v, isProfile (X v))
    {δ Δ Δ' : ℝ} (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2)
    (U : Finset V) (hUv : ∀u ∈ U, (ball u δ).Valid X)
    (hUd : (U : Set V).Pairwise (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (F : Finset (Finset V))
    (hFd : (F : Set (Finset V)).Pairwise Disjoint)
    (hF : ∀D ∈ F, D ⊆ U ∧ D.Nonempty ∧
      (∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ) ∧ 36*Δ ≤ (D.card : ℝ)*δ)
    (O : Finset (RadialShell V)) (hO : Arrangement X O)
    (C : Finset V) (hCU : C ⊆ U) (hCF : ∀D ∈ F, Disjoint C D)
    (hOC : ∀H ∈ O, ∀z ∈ C, Disjoint (H.support X) ((ball z δ).support X)) :
    ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      potential Δ O+(C.card : ℝ)*(δ-6*Δ')+δ/4*∑D ∈ F, (D.card : ℝ) ≤ potential Δ' Z := by
  induction F using Finset.strongInductionOn generalizing O C with
  | _ F ih =>
    by_cases hinter : ∃D ∈ F, ∃z ∈ D, ∃H ∈ O,
      H.inner+δ+Δ ≤ normDistance (X z) (X H.center) ∧
        normDistance (X z) (X H.center) ≤ H.outer-δ-Δ
    · obtain ⟨D,hDF,z,hz,H,hHO,hint⟩ := hinter
      obtain ⟨L,R,hL,hR,hLR,hspan,hbounds⟩ :=
        radial_span (hF D hDF).2.1 (hF D hDF).2.2.1 hz hint
      obtain ⟨P,hP,hPH,hPD,hpot⟩ := split_shells hX (hO.1 H hHO) hδ hΔ hΔ' hnext
        hL hR hLR hspan (hF D hDF).2.2.2
      have hballH : ∀u ∈ D, (ball u δ).support X ⊆ H.support X := by
        intro u hu
        exact ball_subset_of_radial_margin X H u (hL.trans (hbounds u hu).1)
          ((hbounds u hu).2.trans hR)
      have hcross : ∀K ∈ O.erase H, ∀J ∈ P, Disjoint (K.support X) (J.support X) := by
        intro K hK J hJ
        exact (hO.2 (mem_of_mem_erase hK) hHO (ne_of_mem_erase hK)).mono_right (hPH J hJ)
      have hOE := arrangement_subset hO (erase_subset H O)
      have hOP := arrangement_union hOE hP hcross
      have hCUD : C ∪ D ⊆ U := union_subset hCU (hF D hDF).1
      have hCDE : ∀E ∈ F.erase D, Disjoint (C ∪ D) E := by
        intro E hE
        exact disjoint_union_left.mpr ⟨hCF E (mem_of_mem_erase hE),
          hFd hDF (mem_of_mem_erase hE) (ne_of_mem_erase hE).symm⟩
      have hnewOC : ∀K ∈ O.erase H ∪ P, ∀u ∈ C ∪ D,
          Disjoint (K.support X) ((ball u δ).support X) := by
        intro K hK u hu
        rcases mem_union.mp hK with hK | hK <;> rcases mem_union.mp hu with hu | hu
        · exact hOC K (mem_of_mem_erase hK) u hu
        · exact (hO.2 (mem_of_mem_erase hK) hHO (ne_of_mem_erase hK)).mono_right (hballH u hu)
        · exact (hOC H hHO u hu).mono_left (hPH K hK)
        · exact (hPD u (hbounds u hu).1 (hbounds u hu).2 K hK).symm
      obtain ⟨Z,hZ,hZpot⟩ := ih (F.erase D) (erase_ssubset hDF)
        (hFd.mono (erase_subset _ _)) (fun E hE => hF E (mem_of_mem_erase hE))
        (O.erase H ∪ P) hOP (C ∪ D) hCUD hCDE hnewOC
      refine ⟨Z,hZ,?_⟩
      have hp := potential_union (arrangement_disjoint_finsets hX hOE hcross) Δ
      have he := potential_erase hHO Δ
      have hc := card_union_of_disjoint (hCF D hDF)
      have hs := sum_erase_add F (fun E : Finset V => (E.card : ℝ)) hDF
      have hc' : ((C ∪ D).card : ℝ) = (C.card : ℝ)+(D.card : ℝ) := by exact_mod_cast hc
      rw [hp,hc'] at hZpot
      nlinarith
    · obtain ⟨P,hP,hPO,hPF,hpot⟩ := shrink_shells hX hO hδ hΔ hΔ' hnext
      let W := C ∪ F.biUnion id
      have hWU : W ⊆ U := by
        intro u hu
        rcases mem_union.mp hu with hu | hu
        · exact hCU hu
        · obtain ⟨D,hD,hu⟩ := mem_biUnion.mp hu
          exact (hF D hD).1 hu
      have hB : Arrangement X (W.image (fun u => ball u δ)) :=
        arrangement_balls (fun u hu => hUv u (hWU hu)) (hUd.mono hWU)
      have hcross : ∀H ∈ P, ∀K ∈ W.image (fun u => ball u δ),
          Disjoint (H.support X) (K.support X) := by
        intro H hH K hK
        obtain ⟨u,hu,rfl⟩ := mem_image.mp hK
        rcases mem_union.mp hu with hu | hu
        · obtain ⟨J,hJ,hsub⟩ := hPO H hH
          exact (hOC J hJ u hu).mono_left hsub
        · obtain ⟨D,hD,hu⟩ := mem_biUnion.mp hu
          exact (hPF u (fun J hJ hh => hinter ⟨D,hD,u,hu,J,hJ,hh⟩) H hH).symm
      refine ⟨P ∪ W.image (fun u => ball u δ),arrangement_union hP hB hcross,?_⟩
      rw [potential_union (arrangement_disjoint_finsets hX hP hcross),
        potential_balls (show 6*Δ' ≤ δ by linarith)]
      have hCW : Disjoint C (F.biUnion id) := by
        rw [Finset.disjoint_left]
        intro u hu hv
        obtain ⟨D,hD,hv⟩ := mem_biUnion.mp hv
        exact Finset.disjoint_left.mp (hCF D hD) hu hv
      have hflat : (F.biUnion id).card = ∑D ∈ F, D.card := card_biUnion hFd
      have hwcard : (W.card : ℝ) = (C.card : ℝ)+∑D ∈ F, (D.card : ℝ) := by
        dsimp [W]
        rw [card_union_of_disjoint hCW,hflat,Nat.cast_add,Nat.cast_sum]
      rw [hwcard]
      have hsum : 0 ≤ ∑D ∈ F, (D.card : ℝ) := sum_nonneg (fun D _ => Nat.cast_nonneg _)
      have hmass : δ/4*(∑D ∈ F, (D.card : ℝ)) ≤
          (∑D ∈ F, (D.card : ℝ))*(δ-6*Δ') := by nlinarith
      nlinarith

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

lemma compact_arrangement (hX : ∀v, isProfile (X v))
    (q : ℕ) (δ Δ : ℕ → ℝ) (U : ℕ → Finset V) (F : ℕ → Finset (Finset V))
    (hδ : ∀i < q, 0 < δ i) (hΔ : ∀i < q, 2*δ i ≤ Δ i)
    (hΔ0 : ∀i ≤ q, 0 ≤ Δ i) (hnext : ∀i < q, 6*Δ (i+1) ≤ δ i/2)
    (hUv : ∀i < q, ∀u ∈ U i, (ball u (δ i)).Valid X)
    (hUd : ∀i < q, (U i : Set V).Pairwise
      (fun u v => Disjoint ((ball u (δ i)).support X) ((ball v (δ i)).support X)))
    (hFd : ∀i < q, (F i : Set (Finset V)).Pairwise Disjoint)
    (hF : ∀i < q, ∀D ∈ F i, D ⊆ U i ∧ D.Nonempty ∧
      (∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ i) ∧ 36*Δ i ≤ (D.card : ℝ)*δ i) :
    ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      (∑i ∈ range q, δ i*(∑D ∈ F i, (D.card : ℝ)))/4 ≤ potential (Δ q) Z := by
  have hex : ∀j ≤ q, ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      (∑i ∈ range j, δ i*(∑D ∈ F i, (D.card : ℝ)))/4 ≤ potential (Δ j) Z := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨∅,arrangement_empty,by simp [potential]⟩
    | succ j ih =>
      intro hj
      have hjq : j < q := by omega
      obtain ⟨O,hO,hpot⟩ := ih (by omega)
      obtain ⟨Z,hZ,hZp⟩ := compact_phase hX (hδ j hjq) (hΔ j hjq)
        (hΔ0 (j+1) hj) (hnext j hjq) (U j) (hUv j hjq) (hUd j hjq)
        (F j) (hFd j hjq) (hF j hjq) O hO ∅ (empty_subset _) (by simp) (by simp)
      refine ⟨Z,hZ,?_⟩
      simp only [card_empty,Nat.cast_zero,zero_mul,add_zero] at hZp
      rw [sum_range_succ]
      linarith
  exact hex q le_rfl

lemma CompactFamily.ball_valid (hX : ∀v, isProfile (X v)) {δ Δ : ℝ}
    (F : CompactFamily X δ Δ) {u : V} (hu : u ∈ F.bags.biUnion id) :
    (ball u δ).Valid X := by
  obtain ⟨D,hD,huD⟩ := mem_biUnion.mp hu
  have hcard := F.cardinal D hD
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) u
  have hvU : v ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hv⟩
  have hdist := disjoint_balls_distance hX u v (F.balls_disjoint hu hvU hvu.symm)
  refine ⟨le_rfl,F.radius_pos,fun _ => rfl,⟨u,by simp [ball,normDistance_self]⟩,v,?_⟩
  change δ ≤ normDistance (X v) (X u)
  rw [normDistance_comm]
  linarith [F.radius_pos]

lemma CompactFamily.scale (hX : ∀v, isProfile (X v)) {δ Δ : ℝ}
    (F : CompactFamily X δ Δ) : 2*δ ≤ Δ := by
  obtain ⟨D,hD⟩ := F.nonempty
  have hcard := F.cardinal D hD
  obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0 < D.card)
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) u
  have huU : u ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hu⟩
  have hvU : v ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hv⟩
  exact (disjoint_balls_distance hX u v (F.balls_disjoint huU hvU hvu.symm)).trans
    (F.diameter D hD u hu v hv)

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset RadialShell

variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

lemma arrangement_length_bound {n m : ℕ} (G : StrongThinTree.MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → J → ℝ) (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell (Fin n))} (hO : Arrangement X O) :
    (k:ℝ)*potential 0 O ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  classical
  obtain ⟨Y,hY⟩ := Classical.axiomOfChoice hX
  have hXY : X = fun v => profile (Y v) := funext hY
  subst X
  have hb := shell_length_bound G hk Y (fun H : O => Y H.val.center)
    (fun H : O => H.val.inner) (fun H : O => H.val.outer)
    (fun H => (hO.1 H.val H.property).2.1.le)
    (fun H => by
      simpa only [normDistance, profile_norm_sub] using
        (hO.1 H.val H.property).2.2.2.1)
    (fun H => by
      simpa only [normDistance, profile_norm_sub] using
        (hO.1 H.val H.property).2.2.2.2) ?_
  · convert hb using 2
    · rw [potential,Finset.sum_coe_sort O (fun H : RadialShell (Fin n) => H.outer-H.inner)]
      apply sum_congr rfl
      intro H hH
      simp only [capacity,mul_zero,sub_zero]
      exact max_eq_left (valid_width_pos (hO.1 H hH)).le
    · simp only [normDistance,profile_norm_sub]
  · intro H K hne
    apply Set.disjoint_left.mpr
    rintro w ⟨hw, hHa, hHb⟩ ⟨_, hKa, hKb⟩
    exact Set.disjoint_left.mp (hO.2 H.property K.property (Subtype.val_injective.ne hne))
      ⟨hw,hHb,Or.inr hHa⟩ ⟨hw,hKb,Or.inr hKa⟩

lemma metric_compact_bound {n m : ℕ} (G : StrongThinTree.MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → J → ℝ) (hX : ∀v, isProfile (X v))
    (q : ℕ) (δ Δ : ℕ → ℝ) (F : ∀i, CompactFamily X (δ i) (Δ i))
    (hnext : ∀i, i+1 < q → Δ (i+1) ≤ δ i/12) :
    (k:ℝ)/4*(∑i ∈ range q, δ i*(∑D ∈ (F i).bags, (D.card : ℝ))) ≤
      ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let D := fun i => if i < q then Δ i else 0
  have hD0 : ∀i ≤ q, 0 ≤ D i := by
    intro i hi
    dsimp [D]
    split_ifs with hh
    · linarith [(F i).scale hX,(F i).radius_pos]
    · exact le_rfl
  obtain ⟨Z,hZ,hZp⟩ := compact_arrangement hX q δ D
    (fun i => (F i).bags.biUnion id) (fun i => (F i).bags)
    (fun i _ => (F i).radius_pos)
    (fun i hi => by simpa [D,hi] using (F i).scale hX) hD0
    (by
      intro i hi
      dsimp [D]
      split_ifs with hh
      · linarith [hnext i hh]
      · linarith [(F i).radius_pos])
    (fun i _ u hu => (F i).ball_valid hX hu)
    (fun i _ => (F i).balls_disjoint)
    (fun i _ => (F i).bags_disjoint)
    (by
      intro i hi S hS
      refine ⟨?_,?_,?_,?_⟩
      · intro u hu; exact mem_biUnion.mpr ⟨S,hS,hu⟩
      · exact card_pos.mp (by have := (F i).cardinal S hS; omega)
      · simpa [D,hi] using (F i).diameter S hS
      · simpa [D,hi] using (F i).compact S hS)
  simp only [D,lt_self_iff_false,ite_false, if_false] at hZp
  have hmul := mul_le_mul_of_nonneg_left hZp (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hlength := arrangement_length_bound G hk X hX hZ
  nlinarith

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_AssignedGeometry
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric assigned geometry. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (clamp clamped_affine_disjoint_sum)

variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_nonneg (x y : J → ℝ) : 0 ≤ normDistance x y := norm_nonneg _

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ScaleCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric scale charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical

namespace CompactPackage
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

lemma finite_bound {k : ℕ} (hk : G.EdgeConnected k) (hX : ∀v, isProfile (X v))
    {q : ℕ} (F : Fin q → CompactPackage X)
    (hnext : ∀i j : Fin q, i.val+1=j.val → (F j).diameter ≤ (F i).radius/12) :
    (k:ℝ)/4*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  by_cases hq : q=0
  · subst q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero]
    exact sum_nonneg (fun e _ => normDistance_nonneg _ _)
  · have hq' : 0 < q := Nat.pos_of_ne_zero hq
    let ind : ℕ → Fin q := fun i => ⟨i%q,Nat.mod_lt _ hq'⟩
    have hh := metric_compact_bound G hk X hX q
      (fun i => (F (ind i)).radius) (fun i => (F (ind i)).diameter)
      (fun i => (F (ind i)).family) (by
        intro i hi
        apply hnext
        simp only [ind,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (show i<q by omega)])
    have he : (∑i : Fin q, (F i).mass) = ∑i ∈ range q, (F (ind i)).mass := by
      rw [←Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i hi
      have hind : ind i.val=i := by apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt
      rw [hind]
    rw [he]
    exact hh

lemma ordered_bound {J : Type*} [LinearOrder J] {k : ℕ} (hk : G.EdgeConnected k) (hX : ∀v, isProfile (X v))
    (S : Finset J) (F : S → CompactPackage X)
    (hgeo : ∀i j : S, j.val < i.val → (F j).diameter ≤ (F i).radius/12) :
    (k:ℝ)/4*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let e := S.orderIsoOfFin rfl
  let f : Fin S.card ≃ S := Fin.revPerm.trans e.toEquiv
  have hh := finite_bound hk hX (fun i => F (f i)) (by
    intro i j hij
    apply hgeo
    change (e j.rev).val < (e i.rev).val
    exact e.strictMono (Fin.rev_lt_rev.mpr (show i<j by omega)))
  rw [f.sum_comp (fun i => (F i).mass)] at hh
  exact hh
end CompactPackage

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

namespace CapturedFamily
variable {η : ℝ}

lemma mass_nonneg (F : CapturedFamily H G X η) : 0 ≤ F.mass := by
  cases F with
  | inl F => exact mul_nonneg F.family.radius_pos.le (sum_nonneg (fun D _ => Nat.cast_nonneg _))
  | inr F => exact mul_nonneg (sum_nonneg (fun i _ => Nat.cast_nonneg _)) F.positive.le

lemma mixed_bound {J : Type*} [LinearOrder J] {q : ℕ}
    (hq : 0 < q) (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q) {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → CapturedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).upper ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).Ratio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    ((q:ℝ)/8192)*(∑i, (F i).mass) ≤ 2*∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let C : Finset S := univ.filter (fun i => ∃P, F i=Sum.inl P)
  let A : Finset S := univ\C
  have hexC : ∀i : C, ∃P, F i.val=Sum.inl P := fun i => (mem_filter.mp i.property).2
  have hexA : ∀i : A, ∃P, F i.val=Sum.inr P := by
    intro i
    cases hh : F i.val with
    | inl P =>
      have hi : i.val ∉ C := (mem_sdiff.mp i.property).2
      exact (hi (mem_filter.mpr ⟨mem_univ _,⟨P,hh⟩⟩)).elim
    | inr P => exact ⟨P,rfl⟩
  let FC : C → CompactPackage X := fun i => Classical.choose (hexC i)
  let FA : A → AssignedFamily H G X (6144/q) := fun i => Classical.choose (hexA i)
  have hFC : ∀i : C, F i.val=Sum.inl (FC i) := fun i => Classical.choose_spec (hexC i)
  have hFA : ∀i : A, F i.val=Sum.inr (FA i) := fun i => Classical.choose_spec (hexA i)
  have hC := CompactPackage.ordered_bound hk hX C FC (by
    intro i j hij
    have hh := hgeo i.val j.val hij
    rw [hFC i,hFC j] at hh
    change (FC j).diameter ≤ ρ*(FC i).radius at hh
    have hr : ρ ≤ 1/12 := hρsmall.trans (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hr (FC i).family.radius_pos.le
    exact hh.trans (by nlinarith only [hm]))
  have hA := AssignedSequence.ordered_bound hX (show (0:ℝ)<q by exact_mod_cast hq)
    hconn hρ hρsmall A FA (by
      intro i j hij
      have hh := hgeo i.val j.val hij
      rw [hFA i,hFA j] at hh
      exact hh)
    (by intro i; have hh := hR i.val; rw [hFA i] at hh; exact hh)
    (by
      intro i j hij
      have hh := hdis i.val j.val (Subtype.val_injective.ne hij)
      rw [hFA i,hFA j] at hh
      exact hh)
  have hsumC : (∑i : C, (FC i).mass) = ∑i ∈ C, (F i).mass := by
    rw [←sum_coe_sort C (fun i => (F i).mass)]
    apply sum_congr rfl
    intro i hi
    rw [hFC i]
    rfl
  have hsumA : (∑i : A, (FA i).mass) = ∑i ∈ A, (F i).mass := by
    rw [←sum_coe_sort A (fun i => (F i).mass)]
    apply sum_congr rfl
    intro i hi
    rw [hFA i]
    rfl
  rw [hsumC] at hC
  rw [hsumA] at hA
  have hCn : 0 ≤ ∑i ∈ C, (F i).mass := sum_nonneg (fun i _ => mass_nonneg (F i))
  have hcoef : (q:ℝ)/8192 ≤ (q:ℝ)/4 := by
    have hh : (0:ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  have hC' := (mul_le_mul_of_nonneg_right hcoef hCn).trans hC
  have he : (∑i ∈ A, (F i).mass)+(∑i ∈ C, (F i).mass) = ∑i : S, (F i).mass :=
    sum_sdiff (subset_univ C)
  rw [←he,mul_add]
  linarith only [hA,hC']
end CapturedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}
namespace CapturedFamily
lemma scale_bound {q : ℕ} (hq : 0 < q) (hk : G.EdgeConnected q)
    (hX : ∀v, isProfile (X v)) (hconn : LocallyConnectedReal H G q)
    {ρ s : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536) (hs : 0 < s)
    {R : ℕ} (hR : 0 < R) (hlog : Real.logb 2 (24/(ρ*s^2)) < R)
    (S : Finset ℤ) (F : S → CapturedFamily H G X (6144/q))
    (hlow : ∀i : S, s*2^(i.val:ℝ) ≤ (F i).radius)
    (hupp : ∀i : S, (F i).upper ≤ 24*2^(i.val:ℝ)/s)
    (hratio : ∀i, (F i).Ratio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    ((q:ℝ)/8192)*(∑i, (F i).mass) ≤
      2*R*(∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let residue : ℤ → Fin R := fun i => ⟨(i%R).toNat, by
    have hn := Int.emod_nonneg i (show (R:ℤ)≠0 by omega)
    have hh := Int.emod_lt_of_pos i (show (0:ℤ)<R by omega)
    omega⟩
  let C : Fin R → Finset S := fun r => univ.filter (fun i => residue i.val=r)
  have hbound : ∀r : Fin R, ((q:ℝ)/8192)*(∑i ∈ C r, (F i).mass) ≤
      2*∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
    intro r
    have hh := mixed_bound hq hk hX hconn hρ hρsmall (C r) (fun i => F i.val) (by
      intro i j hij
      have hi := (mem_filter.mp i.property).2
      have hj := (mem_filter.mp j.property).2
      have hmod : j.val.val%R=i.val.val%R := by
        have he := congrArg Fin.val (hj.trans hi.symm)
        dsimp [residue] at he
        have hn1 := Int.emod_nonneg i.val.val (show (R:ℤ)≠0 by omega)
        have hn2 := Int.emod_nonneg j.val.val (show (R:ℤ)≠0 by omega)
        omega
      have hsep := ScaleSelection.separated_scales hs hρ hlog
        (ScaleSelection.residue_spacing hR hij hmod)
      exact (hupp j.val).trans (hsep.le.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hlow i.val) hρ.le)))
      (fun i => hratio i.val)
      (fun i j hij => hdis i.val j.val (Subtype.val_injective.ne hij))
    rw [←sum_coe_sort (C r) (fun i => (F i).mass)]
    exact hh
  have hh := sum_le_sum (s := univ) (fun r (_ : r ∈ univ) => hbound r)
  rw [←mul_sum] at hh
  have he : (∑r : Fin R, ∑i ∈ C r, (F i).mass) = ∑i : S, (F i).mass := by
    exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) (fun i => (F i).mass)
  rw [he] at hh
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_left_comm] using hh
end CapturedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma homogeneous_scale_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q)
    (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (idx : Finset (Fin n) → ℤ) (off : Finset (Fin n) → Fin L)
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε ρ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, 2^(idx t:ℝ) ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*2^(idx t:ℝ))
    (hdmin : ∀t ∈ T, ∀e ∈ F t, 2^((idx t:ℝ)+(off t).val) ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ 4*2^((idx t:ℝ)+(off t).val))
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlog : Real.logb 2 (24/(ρ*(α*γ/32)^2)) < R) :
    let s := α*γ/32
    let W := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(W/(L:ℝ)) ≤
      2*R*(∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let s := α*γ/32
  let w : Finset (Fin n) → ℝ := fun t =>
    (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/((parentBoundary H G t).card : ℝ)
  let c := s^ε/(6912*(1024/ε^2))
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hc : 0 ≤ c := by dsimp [c] <;> positivity
  obtain ⟨choice,hchoice⟩ := ScaleSelection.select_fibers T idx off w
  simp only [Fintype.card_fin] at hchoice
  let U := T.filter (fun t => off t=choice (idx t))
  let S := U.image idx
  let B : S → Finset (Finset (Fin n)) := fun i => U.filter (fun t => idx t=i.val)
  have hBT : ∀i : S, B i ⊆ T := fun i => (filter_subset _ _).trans (filter_subset _ _)
  have hBn : ∀i : S, (B i).Nonempty := by
    intro i
    obtain ⟨t,ht,heq⟩ := mem_image.mp i.property
    exact ⟨t,mem_filter.mpr ⟨ht,heq⟩⟩
  have hi : ∀i : S, ∀t ∈ B i, idx t=i.val := fun i t ht => (mem_filter.mp ht).2
  have hoff : ∀i : S, ∀t ∈ B i, off t=choice i.val := by
    intro i t ht
    have hh := (mem_filter.mp (mem_filter.mp ht).1).2
    change off t=choice (idx t) at hh
    rw [hi i t ht] at hh
    exact hh
  have hex : ∀i : S, ∃P : CapturedFamily H G X (6144/q),
      P.owners ⊆ B i ∧ P.Ratio ρ ∧ s*2^(i.val:ℝ) ≤ P.radius ∧
      P.upper ≤ 12*2^(i.val:ℝ)/s ∧ c*(∑t ∈ B i, w t) ≤ P.mass := by
    intro i
    have hp1 : (0:ℝ) < 2^(i.val:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hp2 : (0:ℝ) < 4*2^((i.val:ℝ)+(choice i.val).val) := by positivity
    obtain ⟨P,hP⟩ := capturePackage (B i) F Y (hBn i) ((hBT i).trans hT)
      (fun t ht => hroot t (hBT i ht)) (fun t ht => hF t (hBT i ht))
      (fun t ht => hFn t (hBT i ht)) hα hγ he he1 hp1 hp2 hcontract hpositive
      (by intro t ht e he; simpa only [hi i t ht] using hmin t (hBT i ht) e he)
      (by intro t ht e he; simpa only [hi i t ht] using hmax t (hBT i ht) e he)
      (by
        intro t ht e he
        have hh := hdmin t (hBT i ht) e he
        rw [hi i t ht,hoff i t ht] at hh
        simpa only [mul_div_cancel_left₀ _ (by norm_num : (4:ℝ)≠0)] using hh)
      (by intro t ht e he; simpa only [hi i t ht,hoff i t ht] using hdmax t (hBT i ht) e he)
      (fun t ht => hbad t (hBT i ht)) (fun t ht => hdom t (hBT i ht)) hsmall hassign
      (fun t ht => hratio t (hBT i ht))
    refine ⟨P,hP.1,hP.2.1,hP.2.2.1,hP.2.2.2.1,?_⟩
    simpa only [c,w,div_mul_eq_mul_div] using hP.2.2.2.2
  let P : S → CapturedFamily H G X (6144/q) := fun i => Classical.choose (hex i)
  have hP := fun i => Classical.choose_spec (hex i)
  have hbound := CapturedFamily.scale_bound hq hk hX hconn hρ hρsmall hs hR hlog S P
    (fun i => (hP i).2.2.1)
    (by
      intro i
      apply (hP i).2.2.2.1.trans
      apply div_le_div_of_nonneg_right _ hs.le
      exact mul_le_mul_of_nonneg_right (by norm_num : (12:ℝ)≤24) (Real.rpow_nonneg (by norm_num) _))
    (fun i => (hP i).2.1)
    (by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro t hti htj
      have he := (hi i t ((hP i).1 hti)).symm.trans (hi j t ((hP j).1 htj))
      exact hij (Subtype.ext he))
  have hfiber : (∑i : S, ∑t ∈ B i, w t) = ∑t ∈ U, w t := by
    rw [sum_coe_sort S (fun i => ∑t ∈ U.filter (fun t => idx t=i), w t)]
    exact sum_fiberwise_of_maps_to (fun t ht => mem_image_of_mem idx ht) w
  have hsum : c*(∑t ∈ U, w t) ≤ ∑i : S, (P i).mass := by
    have hh := sum_le_sum (s := univ) (fun i (_ : i ∈ univ) => (hP i).2.2.2.2)
    rw [←mul_sum,hfiber] at hh
    exact hh
  have hgain := (mul_le_mul_of_nonneg_left hchoice hc).trans hsum
  have hq0 : 0 ≤ (q:ℝ)/8192 := by positivity
  have hh := (mul_le_mul_of_nonneg_left hgain hq0).trans hbound
  simpa only [mul_assoc] using hh
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Numerator
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric numerator. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (truncationBins truncationGain truncationGain_pos)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord]
  {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

omit [PseudoMetricSpace Coord] in
lemma diagonal_sq_le (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v)) (e : Fin m) :
    ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ normDistance (X (G.left e)) (X (G.right e)) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (Y (G.left e)-Y (G.right e)) e) 2
  have he : ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ ‖Y (G.left e)-Y (G.right e)‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  exact he.trans (hcontract _ _)

lemma positive_bad_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q)
    (T : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hpos : ∀t ∈ T, 0 < ∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    let N := ∑t ∈ T, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(γ*N/(L:ℝ)) ≤
      2*R*(∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let γ := truncationGain α
  let s := α*γ/32
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => normDistance (X (G.left e)) (X (G.right e))
  let O := parentBoundary H G
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hex : ∀t : Finset (Fin n), ∃B : Finset (Fin m), ∃i : ℤ, ∃o : Fin L,
      t ∈ T → B.Nonempty ∧ B ⊆ O t ∧ γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(i:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(i:ℝ)) ∧
      (∀e ∈ B, 2^((i:ℝ)+o.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((i:ℝ)+o.val)) := by
    intro t
    by_cases ht : t ∈ T
    · have hOn : (O t).Nonempty := by
        by_contra hh
        have heq : O t=∅ := not_nonempty_iff_eq_empty.mp hh
        have hp := hpos t ht
        change 0 < ∑e ∈ O t, a e at hp
        simp only [heq,sum_empty,lt_self_iff_false] at hp
      obtain ⟨B,i,o,hB⟩ := Truncation.scaled_subset (O t) a d hα hα1 hOn
        (fun e _ => hpositive e) (fun e _ => diagonal_sq_le Y hcontract e) (hpos t ht) (hbad t ht) hlogL
      exact ⟨B,i,o,fun _ => hB⟩
    · exact ⟨∅,0,⟨0,hL⟩,fun hh => (ht hh).elim⟩
  choose F idx off hf using hex
  have hh := homogeneous_scale_bound hq hL hR hk hX hconn T F idx off Y hT hroot
    (fun t ht => (hf t ht).2.1) (fun t ht => (hf t ht).1) hα hγ he he1 hρ hρsmall
    hcontract hpositive (fun t ht => (hf t ht).2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.1) (fun t ht => (hf t ht).2.2.2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.2.2) hbad (fun t ht => (hf t ht).2.2.1)
    hsmall hassign hratio hlogR
  have hsum : γ*(∑t ∈ T, (∑e ∈ O t, a e)^2/((O t).card:ℝ)) ≤
      ∑t ∈ T, (∑e ∈ F t, a e)^2/((O t).card:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf t ht).2.2.1 (Nat.cast_nonneg _)
  have hgain := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L : (0:ℝ)≤L)
  have hc : 0 ≤ ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2))) := by positivity
  exact (mul_le_mul_of_nonneg_left hgain hc).trans hh
lemma weighted_boundary_sum (M : Finset (Finset (Fin n)))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    (d : Fin m → ℝ) (hd : ∀e, 0 ≤ d e) :
    (∑t ∈ M, ∑e ∈ parentBoundary H G t, d e) ≤ 2*∑e, d e := by
  have heq : (∑t ∈ M, ∑e ∈ parentBoundary H G t, d e) =
      ∑e, ((M.filter (fun t => e ∈ parentBoundary H G t)).card : ℝ)*d e := by
    calc
      _ = ∑t ∈ M, ∑e : Fin m, if e ∈ parentBoundary H G t then d e else 0 := by
        apply sum_congr rfl
        intro t ht
        rw [←sum_filter]
        simp
      _ = ∑e : Fin m, ∑t ∈ M, if e ∈ parentBoundary H G t then d e else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro e he
        rw [←sum_filter, sum_const,nsmul_eq_mul]
  rw [heq,mul_sum]
  apply sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (hd e)
  exact_mod_cast H.parentBoundary_multiplicity G M hM hroot e

lemma hierarchy_numerator_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q)
    (M : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    (∑t ∈ M, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)) ≤
      (2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ))*
        (∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let O := parentBoundary H G
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => normDistance (X (G.left e)) (X (G.right e))
  let N : Finset (Fin n) → ℝ := fun t => (∑e ∈ O t, a e)^2/((O t).card:ℝ)
  let T := M.filter (fun t => 0 < ∑e ∈ O t, a e ∧
    α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
  have hTM : T ⊆ M := filter_subset _ _
  have hgood : ∀t ∈ M\T, N t ≤ α*∑e ∈ O t, d e := by
    intro t ht
    have htM := (mem_sdiff.mp ht).1
    have htT := (mem_sdiff.mp ht).2
    have hd : 0 ≤ α*∑e ∈ O t, d e := mul_nonneg hα.le (sum_nonneg (fun e _ => normDistance_nonneg _ _))
    by_cases hp : 0 < ∑e ∈ O t, a e
    · have hn : ¬α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2 := by
        intro hh; exact htT (mem_filter.mpr ⟨htM,hp,hh⟩)
      have hc : 0 < ((O t).card:ℝ) := by
        by_contra h
        have hz : (O t).card=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
        have hz' : O t=∅ := card_eq_zero.mp hz
        simp [hz'] at hp
      apply (div_le_iff₀ hc).mpr
      nlinarith only [lt_of_not_ge hn]
    · have hz : ∑e ∈ O t, a e=0 := le_antisymm (le_of_not_gt hp) (sum_nonneg (fun e _ => hpositive e))
      simpa [N,hz] using hd
  have hg : (∑t ∈ M\T, N t) ≤ 2*α*∑e, d e := by
    calc
      (∑t ∈ M\T, N t) ≤ ∑t ∈ M\T, α*∑e ∈ O t, d e := sum_le_sum hgood
      _ = α*∑t ∈ M\T, ∑e ∈ O t, d e := (mul_sum _ _ _).symm
      _ ≤ α*(2*∑e, d e) := mul_le_mul_of_nonneg_left
        (weighted_boundary_sum (M\T) (fun _ ht => hM (mem_sdiff.mp ht).1)
          (fun t ht => hroot t (mem_sdiff.mp ht).1) d (fun _ => normDistance_nonneg _ _)) hα.le
      _ = 2*α*∑e, d e := by ring
  have hb := positive_bad_bound hq hL hR hk hX hconn T Y (hTM.trans hM)
    (fun t ht => hroot t (hTM ht)) hα hα1 he he1 hρ hρsmall hcontract hpositive
    (fun t ht => (mem_filter.mp ht).2.1) (fun t ht => (mem_filter.mp ht).2.2)
    hsmall hassign (fun t ht => hratio t (hTM ht)) hlogL hlogR
  let γ := truncationGain α
  let s := α*γ/32
  let c := ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hL' : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have hb' : (∑t ∈ T, N t) ≤ (2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hh := (div_le_iff₀ hL').mp (show c*(∑t ∈ T, N t)/L ≤ 2*(R:ℝ)*∑e, d e by
      convert hb using 1 ; dsimp [c,N,γ,s,O,a,d] <;> ring)
    nlinarith only [hh]
  change (∑t ∈ M, N t) ≤ (2*α+2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e)
  rw [←sum_sdiff hTM]
  nlinarith only [hg,hb']
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (truncationGain shortcutCoefficient)
open AssignedGeometry CompactGeometry
open scoped Classical
variable {n m : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma squared_euclidean_numerator_bound {q L R : ℕ} (hq : 0 < q)
    (hL : 0 < L) (hR : 0 < R) (hk : G.EdgeConnected q)
    (hconn : LocallyConnectedReal H G q)
    (M : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (p : Fin n → E) (ht : SquaredTriangle p)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ ‖p u-p v‖^2)
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    (∑t ∈ M, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)) ≤
      shortcutCoefficient q L R α ε * (∑e : Fin m, ‖p (G.left e)-p (G.right e)‖^2) := by
  let := squaredPseudoMetric p ht
  have hd (u v : Fin n) : dist u v = ‖p u-p v‖^2 := rfl
  have hc : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (profile (plus u)) (profile (plus v)) := by
    intro u v
    simpa only [normDistance,profile_norm_sub,dist_plus,hd] using hcontract u v
  have hh := AssignedGeometry.hierarchy_numerator_bound hq hL hR hk
    (fun v : Fin n => (show isProfile (profile (plus v)) from ⟨plus v,rfl⟩))
    hconn M Y hM hroot hα hα1 he he1 hρ hρsmall hc hpositive
    hsmall hassign hratio hlogL hlogR
  simpa only [normDistance,profile_norm_sub,dist_plus,hd,shortcutCoefficient] using hh

theorem polynomial_metric_numerator :
    ∀ q : ℕ, 2^2000 ≤ q →
      ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      LocallyConnectedReal H G q →
      ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (parentBoundary H G t).card) →
      ∀ (d : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin d)), SquaredTriangle p →
      ∀ (Y : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀u v, ‖Y u-Y v‖^2 ≤ ‖p u-p v‖^2) →
      (∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e) →
      (∑t ∈ M, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
        ((parentBoundary H G t).card : ℝ)) ≤
        ((q:ℝ)^(-31/40:ℝ)/2)*(∑e : Fin m, ‖p (G.left e)-p (G.right e)‖^2) := by
  have hgood : ∀ q : ℕ, 2^2000 ≤ q → ShortcutNumeric.GoodParameters (q:ℝ) :=
    fun q hq => Q339.Numeric.good_explicit q (by exact_mod_cast hq)
  intro q hq n m G H hconn M hM hroot hratio d p ht Y hcontract hpositive
  have hg := hgood q hq
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity : 0 < 2^2000) hq
  have hqp : (0:ℝ) < q := Nat.cast_pos.mpr hqpos
  have hq1 : (1:ℝ) ≤ q := le_trans (by norm_num) hg.large
  have hα : 0 < ShortcutNumeric.alpha q := Real.rpow_pos_of_pos hqp _
  have hα1 : ShortcutNumeric.alpha q ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have hρ : 0 < ShortcutNumeric.rho q := by dsimp [ShortcutNumeric.rho] <;> positivity
  have hr : ∀t ∈ M, (q:ℝ)*ShortcutNumeric.rho q*((G.cut univ t).card : ℝ) ≤
      (parentBoundary H G t).card := by
    intro t ht
    have heq : (q:ℝ)*ShortcutNumeric.rho q*((G.cut univ t).card : ℝ)=
        ((G.cut univ t).card : ℝ)/q/2 := by
      unfold ShortcutNumeric.rho
      field_simp
    rw [heq]
    have hp : (0:ℝ) ≤ ((G.cut univ t).card : ℝ)/q := div_nonneg (Nat.cast_nonneg _) hqp.le
    exact (by linarith : ((G.cut univ t).card : ℝ)/q/2 ≤
      ((G.cut univ t).card : ℝ)/q).trans (hratio t ht)
  have hb := squared_euclidean_numerator_bound hqpos
    (ShortcutNumeric.count_pos hqp) (ShortcutNumeric.count_pos hqp)
    (Hierarchy.edgeConnected_of_locally hconn) hconn M Y hM hroot hα hα1
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (1/10:ℝ)<1/3)
    hρ hg.rho_small p ht hcontract hpositive
    hg.small hg.assignment hr hg.log_left hg.log_right
  have hcoef : shortcutCoefficient q (ShortcutNumeric.count q) (ShortcutNumeric.count q)
      (ShortcutNumeric.alpha q) (1/10)=ShortcutNumeric.coefficient q := rfl
  rw [hcoef] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hg.coefficient_small
    (sum_nonneg (fun e _ => sq_nonneg _)))

end
end AlgorithmicThinTrees.MetricProfiles
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

lemma eval_difference (x : Fin n → ℝ) (u v : Fin n) :
    x ⬝ᵥ difference u v=x u-x v := by
  simp [difference,point,dotProduct_sub]

lemma gram_distance (X : Matrix (Fin d) (Fin n) ℝ) (u v : Fin n) :
    ‖columnPoints X u-columnPoints X v‖^2=qform (Xᵀ*X) (difference u v) := by
  have hnorm (x : Fin d → ℝ) : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖^2=x ⬝ᵥ x := by
    simp [EuclideanSpace.norm_sq_eq,dotProduct,←pow_two]
  have hv : X *ᵥ difference u v=(fun i => X i u-X i v) := by
    ext i
    exact eval_difference (fun j => X i j) u v
  have hq : qform (Xᵀ*X) (difference u v)=(X *ᵥ difference u v) ⬝ᵥ (X *ᵥ difference u v) := by
    rw [qform,←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  rw [hq,hv,←hnorm]
  rfl

lemma sqrt_gram {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) :
    (CFC.sqrt Z)ᵀ*CFC.sqrt Z=Z := by
  rw [isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg Z).posSemidef.isHermitian]
  exact CFC.sqrt_mul_sqrt_self Z hZ.nonneg

lemma sqrt_columns_metric {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    MetricProfiles.SquaredTriangle (columnPoints (CFC.sqrt Z)) := by
  intro u v w
  simpa only [gram_distance,sqrt_gram hZ.1] using hZ.2 u v w

lemma contraction (X : Matrix (Fin d) (Fin n) ℝ) (U : Matrix (Fin m) (Fin d) ℝ)
    (hU : Uᵀ*U ≤ 1) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    ∀u v, ‖Y u-Y v‖^2 ≤ ‖columnPoints X u-columnPoints X v‖^2 := by
  intro Y u v
  have hh := StrongThinTree.Polar.norm_sq_mulVec_le hU (fun i => X i u-X i v)
  have heq : Y u-Y v=WithLp.toLp 2 (U *ᵥ (fun i => X i u-X i v)) := by
    dsimp [Y]
    rw [show (fun i => X i u-X i v)=(fun i => X i u)-(fun i => X i v) from rfl,mulVec_sub]
    rfl
  rw [heq]
  simpa [EuclideanSpace.norm_sq_eq,dotProduct,columnPoints,←pow_two] using hh

lemma laplacian_pairing (G : MultiGraph n m) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (G.laplacian univ*Z).trace=∑e, qform Z (G.incidence e) := by
  simp only [laplacian,sum_mul,trace_sum,ShortcutDual.trace_outer_mul,qform]

lemma column_edge_energy (G : MultiGraph n m) (X : Matrix (Fin d) (Fin n) ℝ) :
    (∑e, ‖columnPoints X (G.left e)-columnPoints X (G.right e)‖^2)=
      (G.laplacian univ*(Xᵀ*X)).trace := by
  rw [laplacian_pairing]
  apply sum_congr rfl
  intro e _
  exact gram_distance X (G.left e) (G.right e)

theorem polynomial_nuclear_bound_explicit_oai :
    ∀ q : ℕ, 2^2000 ≤ q →
      ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      H.LocallyConnectedReal G q →
      ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
      ∀ (Z : Matrix (Fin n) (Fin n) ℝ), Test Z →
      ∀ (lam : M → ℝ), (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
        (fun t : M => H.parentBoundary G t) lam*CFC.sqrt Z)).trace^2 ≤
        ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace := by
  have hbound := MetricProfiles.polynomial_metric_numerator
  intro q hq n m G H hconn M hM hroot hratio Z hZ lam hlam hsum
  let X := CFC.sqrt Z
  have hn := ShortcutDual.nuclear_bound_of_embedding_bound G.incidence
    (fun t : M => H.parentBoundary G t) X (K := ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace) ?_ hlam hsum
  · simpa only [X,sqrt_gram hZ.1] using hn
  intro U hU hpos
  let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
  have he := hbound q hq n m G H hconn M hM hroot hratio n (columnPoints X)
    (sqrt_columns_metric hZ) Y (contraction X U hU)
    (fun e => by simpa only [Y,G.contraction_edge_diag] using hpos e)
  rw [sum_coe_sort M (fun t => (∑e ∈ H.parentBoundary G t,
    (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2 /
      ((H.parentBoundary G t).card : ℝ))]
  dsimp only [Y] at he
  simp only [G.contraction_edge_diag] at he
  change (∑t ∈ M, _) ≤ _ at he
  rw [column_edge_energy,show Xᵀ*X=Z from sqrt_gram hZ.1] at he
  exact he

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound_explicit_oai := @OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound_explicit_oai
