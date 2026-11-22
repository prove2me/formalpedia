-- Prove2me | solution 1 for MasulloRH.actual_zeta_zero_trace_absolute_little_o_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:05:08.836264+00:00
-- url     : https://prove2.me/submissions/c34a0b97-6131-40ef-96e7-f041ab333ac1

import Mathlib
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_Zeta23_WeilEF_EF_zero_sum_summable_gen
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
open Filter Topology Zeta23
theorem solution (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k) :
    Tendsto (fun L : ℝ => ∑' ρ : {ρ : ℂ // IsNontrivialZero ρ},
      ‖(zeroMult ρ : ℂ) * paperFT k (gammaOf ρ)‖ *
        Real.exp (((ρ : ℂ).re - 1) * L)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hN⟩ := Zeta23.RvM.zeta_local_zero_count
  let Z := Zeta23.zetaZeroConfig
  have hz : ∀ t : ℝ, (Z.N t (t+1) : ℝ) ≤ A * Real.log (|t|+3) := by
    exact hN
  have hs := Zeta23.WeilEF.EF_zero_sum_summable_gen Z hA hz hk hc
  let a := fun ρ : {ρ : ℂ // IsNontrivialZero ρ} =>
    ‖(zeroMult ρ : ℂ) * paperFT k (gammaOf ρ)‖
  have ha : Summable a := hs.norm
  have hlim : Tendsto (fun L : ℝ => ∑' ρ, a ρ * Real.exp (((ρ : ℂ).re-1)*L))
      atTop (𝓝 (∑' _ : {ρ : ℂ // IsNontrivialZero ρ}, (0:ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence ha
    · intro ρ
      have hneg : (ρ : ℂ).re-1 < 0 := sub_neg.mpr ρ.property.2.2
      have he : Tendsto (fun L : ℝ => Real.exp (((ρ : ℂ).re-1)*L)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id)
      simpa using (tendsto_const_nhds (x := a ρ)).mul he
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
      intro ρ
      have ha0 : 0 ≤ a ρ := norm_nonneg _
      have he : Real.exp (((ρ : ℂ).re-1)*L) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ρ.property.2.2.le) hL)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ha0 (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right ha0 he
  simpa [a] using hlim
