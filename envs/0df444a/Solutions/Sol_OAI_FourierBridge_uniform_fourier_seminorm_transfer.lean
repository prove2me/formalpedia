-- Prove2me | solution 1 for OAI.FourierBridge.uniform_fourier_seminorm_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:08.293212+00:00
-- url     : https://prove2.me/submissions/422fc8dd-279a-49e1-b6c3-25b061bfb921

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_fourier_seminorm_from_derivative_integrals

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
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (_hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := by
  let V : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hI (i : ℕ) (hi : i ≤ k) :
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤ V * C := by
    have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume g 0 i
    have hbase' :
        (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) := by
      simpa [V] using hbase
    calc
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          S * (V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) :=
        mul_le_mul_of_nonneg_left hbase' hS
      _ = V * (S * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) := by ring
      _ ≤ V * C := mul_le_mul_of_nonneg_left (hsource i hi) hV
  have hFourier := fourier_seminorm_from_derivative_integrals g k
  calc
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      S * ((2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) :=
      mul_le_mul_of_nonneg_left hFourier hS
    _ = (2 : ℝ) ^ k *
      ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        S * (∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ (2 : ℝ) ^ k *
      ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), V * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p.1 = 0 := by
        have hlt := Finset.mem_range.mp (Finset.mem_product.mp hp).1
        omega
      have hp2 : p.2 ≤ k := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      simpa [hp0] using hI p.2 hp2
    _ = (2 : ℝ) ^ k * (k + 1) * V * C := by
      simp []
      ring
    _ = (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := rfl
end OAI.FourierBridge
