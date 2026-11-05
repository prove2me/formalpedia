-- Prove2me | solution 1 for LL_Decomp1535a.split_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:00.76391+00:00
-- url     : https://prove2.me/submissions/1411bf55-3a6c-400d-a39e-122817304887

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

theorem GbAAux.split_arcs (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in Set.Ioc (0 : ℝ) 1, LL_Decomp1535a.F N α =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, LL_Decomp1535a.F N α) +
        ∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α := by
  have hint : IntegrableOn (LL_Decomp1535a.F N) (Set.Ioc (0 : ℝ) 1) :=
    (GbAAux.continuous_F N).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  exact (integral_inter_add_sdiff hM hint).symm

theorem solution (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in Set.Ioc (0 : ℝ) 1, LL_Decomp1535a.F N α =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, LL_Decomp1535a.F N α) +
        ∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α :=
  GbAAux.split_arcs N hM
