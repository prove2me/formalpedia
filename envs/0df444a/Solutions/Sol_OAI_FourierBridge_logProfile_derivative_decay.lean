-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_derivative_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:05.293208+00:00
-- url     : https://prove2.me/submissions/8a9ab9db-25c7-4980-bd27-2ee651d8f26d

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_coupled_factor_uniform_derivative

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    (W F : ℝ → ℂ) (R a m H CW CF : ℝ) (A n : ℕ)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧ Real.exp (a * y) ≤ H)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (y : ℝ) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp (a * z))) :=
    hFs.comp harg
  have hprod := norm_iteratedFDeriv_mul_le hWs hG y (n := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      (m ^ (A + n) * (1 + R) ^ A) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
          ‖iteratedFDeriv ℝ (n - i)
            (fun z : ℝ => F (R * Real.exp (a * z))) y‖) :=
      mul_le_mul_of_nonneg_left hprod hscale
    _ = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
          ((m ^ (A + n) * (1 + R) ^ A) *
            ‖iteratedFDeriv ℝ (n - i)
              (fun z : ℝ => F (R * Real.exp (a * z))) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hWi : ‖iteratedFDeriv ℝ i W y‖ = 0
      · simp [hWi]
        positivity
      obtain ⟨hLower, hUpper⟩ := hwindow y ⟨i, hi', hWi⟩
      have hGbound := coupled_factor_uniform_derivative F R a y m H CF A n
        (n - i) hFs hR hm hm1 hH ha hLower hUpper (Nat.sub_le n i)
        hCF hFdecay
      have hWbound := hWderiv i hi' y
      gcongr
end OAI.FourierBridge
