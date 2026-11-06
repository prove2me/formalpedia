-- Prove2me | solution 1 for OAI.LocalLogFourier.positive_log_uniform_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:41.015295+00:00
-- url     : https://prove2.me/submissions/a633d163-494e-4e7c-ad8a-96cdbd1b7a47

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_LocalLogFourier_positive_log_product_derivative_bound
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open OAI.LocalLogFourier
namespace OAI.LocalLogFourier
theorem _root_.solution
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A n k : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n)
        (positiveLogProfile V F R hVc hVs hFpos hR) ≤
      Lwin ^ k *
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF) := by
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  let S := m ^ A * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF
  have hS : 0 < S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ Lwin ^ k * C := by positivity
  have hgeq : (g : ℝ → ℂ) =
      fun z => V z * F (R * Real.exp z) := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hFpos hR
  have hpoint (s : ℝ) :
      S * (|s| ^ k * ‖iteratedDeriv n g s‖) ≤ Lwin ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
    · obtain ⟨hms, habs⟩ := hwindow s hactive
      have hraw := positive_log_product_derivative_bound
        V F R m CW CF A n hVs hFpos hR hm hm1
        hCW hCF hVderiv
        (by intro z hz; exact (hwindow z hz).1)
        hEuler s
      have hnorm : S * ‖iteratedDeriv n g s‖ ≤ C := by
        rw [hgeq]
        simpa [S, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        S * (|s| ^ k * ‖iteratedDeriv n g s‖) =
          |s| ^ k * (S * ‖iteratedDeriv n g s‖) := by ring
        _ ≤ |s| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ Lwin ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i V s‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp z)) := by
        simpa only [Function.comp_def] using
          hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
      have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp z)) s‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g s‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => V z * F (R * Real.exp z)) s‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ Lwin ^ k * C / S := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hS.le)
    intro s
    exact (le_div_iff₀ hS).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint s)
  calc
    S * (SchwartzMap.seminorm ℝ k n) g ≤ S * (Lwin ^ k * C / S) :=
      mul_le_mul_of_nonneg_left hsemi hS.le
    _ = Lwin ^ k * C := by field_simp
end OAI.LocalLogFourier
