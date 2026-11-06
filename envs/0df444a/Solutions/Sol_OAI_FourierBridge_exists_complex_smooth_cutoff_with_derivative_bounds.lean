-- Prove2me | solution 1 for OAI.FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:25.959863+00:00
-- url     : https://prove2.me/submissions/f19efce8-db14-4805-821a-a81494a10271

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_exists_complex_smooth_cutoff

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
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by
  obtain ⟨V, hVc, hVs, hVone, hVsupport, _⟩ :=
    exists_complex_smooth_cutoff T hT
  let g : 𝓢(ℝ, ℂ) := hVc.toSchwartzMap hVs
  let CW : ℝ := ∑ i ∈ Finset.range (K + 1), (SchwartzMap.seminorm ℝ 0 i) g
  have hCW : 0 ≤ CW := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hVderiv : ∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW := by
    intro i hi y
    change ‖iteratedFDeriv ℝ i (g : ℝ → ℂ) y‖ ≤ CW
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g i y).trans
      (Finset.single_le_sum (fun _ _ => apply_nonneg _ _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  refine ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, ?_⟩
  intro y hy
  obtain ⟨i, hi, hnonzero⟩ := hy
  have hyderiv : y ∈ Function.support (iteratedFDeriv ℝ i V) := by
    simpa [Function.mem_support] using hnonzero
  have hysupport : y ∈ tsupport V :=
    (support_iteratedFDeriv_subset i) hyderiv
  have hyinterval := hVsupport hysupport
  have hylower : -(T + 1) ≤ y := hyinterval.1
  have hyupper : y ≤ T + 1 := hyinterval.2
  constructor
  · exact Real.exp_le_exp.mpr hylower
  constructor
  · exact Real.exp_le_exp.mpr hyupper
  · exact abs_le.mpr ⟨hylower, hyupper⟩
end OAI.FourierBridge
