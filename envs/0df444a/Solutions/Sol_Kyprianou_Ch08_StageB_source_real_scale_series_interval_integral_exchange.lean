-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_scale_series_interval_integral_exchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:31:05.226094+00:00
-- url     : https://prove2.me/submissions/936c44dc-390a-47ca-b372-3188449eac94

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_interval_mass_summable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_interval_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
import Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    Summable (fun n : ℕ => q ^ n *
      (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)) ∧
    (∫ y in (0 : ℝ)..x,
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n y)) =
    ∑' n : ℕ, q ^ n *
      (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) := by
  let F : ℕ → ℝ → ℝ := fun n y =>
    q ^ n * scaleConvolutionPower (W 0) n y
  have hm := source_scale_discount_interval_mass_summable ψ W hW x q hx hq
  have hmrewrite :
      (fun n : ℕ => ∫ y in (0 : ℝ)..x,
        q ^ n * scaleConvolutionPower (W 0) n y) =
      (fun n : ℕ => q ^ n *
        (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)) := by
    funext n
    rw [intervalIntegral.integral_const_mul]
  rw [hmrewrite] at hm
  have hFi : ∀ n : ℕ, Integrable (F n)
      (volume.restrict (Set.Ioc (0 : ℝ) x)) := by
    intro n
    have hh := (source_scale_power_interval_integrable ψ W hW x hx.le) n
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp hh
    exact hi.const_mul _
  have hpos : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ F n y := by
    intro n y
    exact mul_nonneg (pow_nonneg hq _)
      (source_scale_power_nonnegative_all_real ψ W hW n y)
  have heq : (fun n : ℕ => ∫ y in Set.Ioc (0 : ℝ) x, F n y ∂volume) =
      (fun n : ℕ => q ^ n *
        (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)) := by
    funext n
    dsimp [F]
    rw [integral_const_mul, intervalIntegral.integral_of_le hx.le]
  have hmass : Summable
      (fun n : ℕ => ∫ y in Set.Ioc (0 : ℝ) x, F n y ∂volume) := by
    rw [heq]
    exact hm
  have hs := AvramDividend.Classical.nonnegative_renewal_integral_tsum_exchange
    (volume.restrict (Set.Ioc (0 : ℝ) x)) F hFi hpos hmass
  have hident :
      (∫ y in (0 : ℝ)..x, ∑' n : ℕ, F n y) =
      ∑' n : ℕ, q ^ n *
        (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) := by
    calc
      (∫ y in (0 : ℝ)..x, ∑' n : ℕ, F n y) =
        ∫ y in Set.Ioc (0 : ℝ) x, ∑' n : ℕ, F n y ∂volume :=
          intervalIntegral.integral_of_le hx.le
      _ = ∑' n : ℕ, ∫ y in Set.Ioc (0 : ℝ) x, F n y ∂volume := hs
      _ = ∑' n : ℕ, q ^ n *
          (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) := by
            rw [heq]
  exact ⟨hm, hident⟩
