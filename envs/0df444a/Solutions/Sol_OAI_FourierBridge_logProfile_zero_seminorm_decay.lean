-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_zero_seminorm_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:28.375193+00:00
-- url     : https://prove2.me/submissions/818a7d77-fd22-4dbb-abfe-1d411096141e

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_logProfile_apply
import Theorems.Thm_OAI_FourierBridge_logProfile_pointwise_decay

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
    (W F : ℝ → ℂ) (R a m CW CF : ℝ) (A : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWbound : ∀ y, ‖W y‖ ≤ CW)
    (hlower : ∀ y, W y ≠ 0 → m ≤ Real.exp (a * y))
    (hFdecay : ∀ u, 0 ≤ u → (1 + u) ^ A * ‖F u‖ ≤ CF)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ 0 0) (logProfile W F R a hWc hWs hFs) ≤
      CW * CF := by
  let g := logProfile W F R a hWc hWs hFs
  let scale := m ^ A * (1 + R) ^ A
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hnum : 0 ≤ CW * CF := mul_nonneg hCW hCF
  have hbound : ∀ y, ‖g y‖ ≤ CW * CF / scale := by
    intro y
    apply (le_div_iff₀ hscale).mpr
    have hp := logProfile_pointwise_decay W F R a m CW CF A hR hm hm1
      hCW hCF hWbound hlower hFdecay y
    simpa [g, scale, logProfile_apply, mul_comm, mul_left_comm, mul_assoc] using hp
  have hsemi : (SchwartzMap.seminorm ℝ 0 0) g ≤ CW * CF / scale := by
    apply SchwartzMap.seminorm_le_bound ℝ 0 0 g (div_nonneg hnum hscale.le)
    intro y
    simpa using hbound y
  calc
    scale * (SchwartzMap.seminorm ℝ 0 0) g ≤ scale * (CW * CF / scale) :=
      mul_le_mul_of_nonneg_left hsemi hscale.le
    _ = CW * CF := by field_simp
end OAI.FourierBridge
