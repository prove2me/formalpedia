-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_inverse_slope_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:16.712524+00:00
-- url     : https://prove2.me/submissions/ddd4b8d2-c442-4bb7-aa98-7283bc44d29b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_psi_differentiable_pos
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / ((n : ℝ) + 1)) /
      (ψ (Phi ψ q + 1 / ((n : ℝ) + 1)) - q))) atTop
      (𝓝 (ENNReal.ofReal (deriv (Phi ψ) q))) := by
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hlim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl (by norm_num)).2
  have hroot := (hW q hq.le).1.2.1
  have hr : 0 < Phi ψ q := by
    by_contra hn
    have hz : Phi ψ q = 0 := le_antisymm (le_of_not_gt hn) hroot.1
    have hv := hroot.2
    rw [hz, hzero] at hv
    exact hq.ne hv
  obtain ⟨hp, hd⟩ := p2m89_phi_derivative_exact D ψ W hψ hW q hq
  have hslope := (p2m89_psi_differentiable_pos Ω P D ψ hψ _ hr).hasDerivAt.tendsto_slope_zero_right
  have hs' : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hs⟩
  have hquot : Tendsto (fun n => (s n)⁻¹ * (ψ (Phi ψ q + s n) - q))
      atTop (𝓝 (deriv ψ (Phi ψ q))) := by
    simpa only [smul_eq_mul, Function.comp_def, hroot.2] using hslope.comp hs'
  have hInv := ENNReal.tendsto_ofReal (hquot.inv₀ hp.ne')
  rw [hd]
  apply hInv.congr'
  apply Eventually.of_forall
  intro n
  change ENNReal.ofReal (((s n)⁻¹ * (ψ (Phi ψ q + s n) - q))⁻¹) =
    ENNReal.ofReal (s n / (ψ (Phi ψ q + s n) - q))
  rw [mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]
