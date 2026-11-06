-- Prove2me | solution 1 for OAI.FourierBridge.uniform_logProfile_source_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:32.896786+00:00
-- url     : https://prove2.me/submissions/f5e78822-bef6-4dda-a873-9d0c93333a84

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_logProfile_uniform_seminorm

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
    (W F : ℝ → ℂ) (R a m H L CW CF C : ℝ) (A K n : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hWderiv : ∀ i ≤ K, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ K, ∀ i ≤ j, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant j H CW CF ≤ C) :
    (m ^ (A + K) * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (logProfile W F R a hWc hWs hFs) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (logProfile W F R a hWc hWs hFs)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := profileDerivativeConstant n H CW CF
  let g := logProfile W F R a hWc hWs hFs
  have hWderiv_n : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW := by
    intro i hi y
    exact hWderiv i (hi.trans hn) y
  have hwindow_n : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L := by
    intro y hy
    obtain ⟨i, hi, hnonzero⟩ := hy
    exact hwindow y ⟨i, hi.trans hn, hnonzero⟩
  have hFdecay_n : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF :=
    hFdecay n hn
  have hzero := logProfile_uniform_seminorm W F R a m H L CW CF A n 0
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    hWderiv_n hwindow_n hFdecay_n
  have hp := logProfile_uniform_seminorm W F R a m H L CW CF A n p
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    hWderiv_n hwindow_n hFdecay_n
  have hscale : m ^ (A + K) * (1 + R) ^ A ≤
      m ^ (A + n) * (1 + R) ^ A :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hm.le hm1 (by omega)) (by positivity)
  have hsemi0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 n) g := by positivity
  have hsemip : 0 ≤ (SchwartzMap.seminorm ℝ p n) g := by positivity
  have hzero' : (m ^ (A + K) * (1 + R) ^ A) *
      (SchwartzMap.seminorm ℝ 0 n) g ≤ D := by
    calc
      _ ≤ (m ^ (A + n) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g :=
        mul_le_mul_of_nonneg_right hscale hsemi0
      _ ≤ D := by simpa [D, profileDerivativeConstant, g] using hzero
  have hp' : (m ^ (A + K) * (1 + R) ^ A) *
      (SchwartzMap.seminorm ℝ p n) g ≤ L ^ p * D := by
    calc
      _ ≤ (m ^ (A + n) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g :=
        mul_le_mul_of_nonneg_right hscale hsemip
      _ ≤ L ^ p * D := by simpa [D, profileDerivativeConstant, g, p] using hp
  calc
    (m ^ (A + K) * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ (A + K) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ (A + K) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + L ^ p * D := add_le_add hzero' hp'
    _ = (1 + L ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn
end OAI.FourierBridge
