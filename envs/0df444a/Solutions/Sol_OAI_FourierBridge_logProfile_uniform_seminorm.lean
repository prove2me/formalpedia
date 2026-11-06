-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_uniform_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:46.019996+00:00
-- url     : https://prove2.me/submissions/9b898fe4-5be5-4f62-8721-35f81a811bcd

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_logProfile_apply
import Theorems.Thm_OAI_FourierBridge_logProfile_derivative_decay

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
    (W F : ℝ → ℂ) (R a m H L CW CF : ℝ) (A n k : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n) (logProfile W F R a hWc hWs hFs) ≤
      L ^ k * (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i))) := by
  let g := logProfile W F R a hWc hWs hFs
  have hgeq : (g : ℝ → ℂ) = fun z => W z * F (R * Real.exp (a * z)) := by
    funext z
    exact logProfile_apply W F R a z hWc hWs hFs
  let scale := m ^ (A + n) * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i))
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ L ^ k * C := by positivity
  have hpoint (y : ℝ) :
      scale * (|y| ^ k * ‖iteratedDeriv n g y‖) ≤ L ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0
    · obtain ⟨hlower, hupper, habs⟩ := hwindow y hactive
      have hraw := logProfile_derivative_decay W F R a m H CW CF A n
        hWs hFs hR hm hm1 hH ha hCW hCF hWderiv
        (by intro z hz; obtain ⟨h₁,h₂,_⟩ := hwindow z hz; exact ⟨h₁,h₂⟩)
        hFdecay y
      have hnorm : scale * ‖iteratedDeriv n g y‖ ≤ C := by
        rw [hgeq]
        simpa [scale, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        scale * (|y| ^ k * ‖iteratedDeriv n g y‖) =
          |y| ^ k * (scale * ‖iteratedDeriv n g y‖) := by ring
        _ ≤ |y| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ L ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i W y‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp (a * z))) :=
        hFs.comp harg
      have hprod := norm_iteratedFDeriv_mul_le hWs hG y (n := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp (a * z))) y‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g y‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ L ^ k * C / scale := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hscale.le)
    intro y
    exact (le_div_iff₀ hscale).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint y)
  calc
    scale * (SchwartzMap.seminorm ℝ k n) g ≤ scale * (L ^ k * C / scale) :=
      mul_le_mul_of_nonneg_left hsemi hscale.le
    _ = L ^ k * C := by field_simp
end OAI.FourierBridge
