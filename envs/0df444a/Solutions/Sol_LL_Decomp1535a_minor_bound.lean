-- Prove2me | solution 1 for LL_Decomp1535a.minor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:01.527903+00:00
-- url     : https://prove2.me/submissions/db23c5fc-c16e-433f-870a-bf51fd87bf2f

import Mathlib
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F

open MeasureTheory

theorem GbAAux.continuous_S (N : ℕ) : Continuous (LL_Decomp1535a.S N) := by
  unfold LL_Decomp1535a.S
  apply continuous_finset_sum
  intro p _
  fun_prop

theorem GbAAux.continuous_F (N : ℕ) : Continuous (LL_Decomp1535a.F N) := by
  unfold LL_Decomp1535a.F
  have := GbAAux.continuous_S N
  fun_prop

theorem GbAAux.norm_F (N : ℕ) (α : ℝ) :
    ‖LL_Decomp1535a.F N α‖ = ‖LL_Decomp1535a.S N α‖ ^ 3 := by
  unfold LL_Decomp1535a.F
  rw [norm_mul, norm_pow, Complex.norm_exp]
  simp

theorem GbAAux.minor_bound (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖LL_Decomp1535a.S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α‖ ≤
      B * ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 := by
  have hcont : Continuous fun α => B * ‖LL_Decomp1535a.S N α‖ ^ 2 := by
    have := GbAAux.continuous_S N
    fun_prop
  have hgint : IntegrableOn (fun α => B * ‖LL_Decomp1535a.S N α‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hmeas : MeasurableSet (Set.Ioc (0 : ℝ) 1 \ M) := measurableSet_Ioc.diff hM
  calc ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α‖
      ≤ ∫ α in Set.Ioc (0 : ℝ) 1 \ M, B * ‖LL_Decomp1535a.S N α‖ ^ 2 := by
        refine norm_integral_le_of_norm_le (hgint.mono_set Set.diff_subset) ?_
        filter_upwards [ae_restrict_mem hmeas] with α hα
        rw [GbAAux.norm_F, pow_succ, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hB α hα) (by positivity)
    _ ≤ ∫ α in Set.Ioc (0 : ℝ) 1, B * ‖LL_Decomp1535a.S N α‖ ^ 2 := by
        refine setIntegral_mono_set hgint ?_ (Filter.Eventually.of_forall Set.diff_subset)
        exact Filter.Eventually.of_forall fun α => by positivity
    _ = B * ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_const_mul]

theorem solution (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖LL_Decomp1535a.S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α‖ ≤
      B * ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 :=
  GbAAux.minor_bound N hM hB0 hB
