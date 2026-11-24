-- Prove2me | solution 1 for GeoProdPow.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:54.532786+00:00
-- url     : https://prove2.me/submissions/c1d0b87b-fd62-40cd-b4cf-ee1b72a39657

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd
import Theorems.Thm_GeoProdPow_one_sub_sum_le_prod
import Theorems.Thm_GeoProdPow_geom_le
import Theorems.Thm_GeoProdPow_prod_split
import Theorems.Thm_GeoProdPow_one_sub_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GeoProdPow
open Finset
namespace GeoProdPow
theorem _root_.solution : ConditionalKappaBounds.G2.GaussianProductPowerBound := by
  intro f k r b g0 g1 hf hfk hb hg0 hg1
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hf.trans hfk
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hfk' : (f : ℝ) ≤ k := by exact_mod_cast hfk
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 256 * (k : ℝ) ^ 8 - 1 := ⟨_, rfl⟩
  have hk8 : (1 : ℝ) ≤ (k : ℝ) ^ 8 := one_le_pow₀ hk
  have hG : 256 * (k : ℝ) ^ 8 ≤ ((k : ℝ) * b) ^ 8 := by
    rw [mul_pow]
    have hb8 : (2 : ℝ) ^ 8 ≤ b ^ 8 := pow_le_pow_left₀ (by norm_num) hb 8
    nlinarith
  have hD255 : 255 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hA0 : D + 1 ≤ g0 := by linarith
  have hA1 : D + 1 ≤ g1 := by linarith
  have hg0p : 0 < g0 := by linarith
  have hg1p : 0 < g1 := by linarith
  have hs0 : ∑ i ∈ Ico 1 r, (g0⁻¹) ^ i ≤ 1 / D :=
    (geom_le g0 (by linarith) r).trans (one_div_le_one_div_of_le hDpos (by linarith))
  have hs1 : ∑ i ∈ Ico 1 r, (g1⁻¹) ^ i ≤ 1 / D :=
    (geom_le g1 (by linarith) r).trans (one_div_le_one_div_of_le hDpos (by linarith))
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i ∈ Ico 1 r, ((g0⁻¹) ^ i + (g1⁻¹) ^ i) := ⟨_, rfl⟩
  have hS : S ≤ 2 / D := by
    have e2 : 2 / D = 1 / D + 1 / D := by ring
    rw [hSdef, Finset.sum_add_distrib, e2]
    linarith
  have h2D : 2 / D ≤ 1 := (div_le_one hDpos).2 (by linarith)
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∏ i ∈ Ico 1 r, ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) :=
    ⟨_, rfl⟩
  have hx0 : 0 ≤ g0⁻¹ := inv_nonneg.2 hg0p.le
  have hx1 : 0 ≤ g1⁻¹ := inv_nonneg.2 hg1p.le
  have hy0 : g0⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hy1 : g1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hP : 1 - S ≤ P := by
    rw [hSdef, hPdef]
    apply one_sub_sum_le_prod
    · intro i _
      exact mul_nonneg (one_sub_pow_mem _ hx0 hy0 i).1 (one_sub_pow_mem _ hx1 hy1 i).1
    · intro i _
      exact mul_le_one₀ (one_sub_pow_mem _ hx0 hy0 i).2 (one_sub_pow_mem _ hx1 hy1 i).1
        (one_sub_pow_mem _ hx1 hy1 i).2
    · intro i _
      nlinarith [mul_nonneg (pow_nonneg hx0 i) (pow_nonneg hx1 i)]
  have hS0 : 0 ≤ 1 - S := by linarith
  have hB : 1 + (f : ℝ) * (-S) ≤ (1 + -S) ^ f := one_add_mul_le_pow (by linarith) f
  have hPf : (1 - S) ^ f ≤ P ^ f := pow_le_pow_left₀ hS0 hP f
  have hf4 : (f : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) hfk' 4
  have hk87 : (k : ℝ) ^ 7 ≤ (k : ℝ) ^ 8 := pow_le_pow_right₀ hk (by norm_num)
  have hk7 : (1 : ℝ) ≤ (k : ℝ) ^ 7 := one_le_pow₀ hk
  have hfk3 : (f : ℝ) ^ 4 * (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 7 := by
    calc (f : ℝ) ^ 4 * (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hf4 (by positivity)
      _ = (k : ℝ) ^ 7 := by ring
  have key : 2 * (f : ℝ) / D ≤ 1 / (4 * ((f : ℝ) * k) ^ 3) := by
    rw [div_le_div_iff₀ hDpos (by positivity)]
    have e : 2 * (f : ℝ) * (4 * ((f : ℝ) * k) ^ 3) = 8 * ((f : ℝ) ^ 4 * (k : ℝ) ^ 3) := by ring
    rw [e]
    linarith
  have hfS : (f : ℝ) * S ≤ 2 * (f : ℝ) / D := by
    have : (f : ℝ) * S ≤ (f : ℝ) * (2 / D) := mul_le_mul_of_nonneg_left hS (by linarith)
    linarith [show (f : ℝ) * (2 / D) = 2 * (f : ℝ) / D by ring]
  have hinv : (((f : ℝ) * k) ^ 3)⁻¹ / 4 = 1 / (4 * ((f : ℝ) * k) ^ 3) := by ring
  have hc : 1 - (((f : ℝ) * k) ^ 3)⁻¹ / 4 ≤ P ^ f := by
    rw [hinv]
    have : (1 + -S) = 1 - S := by ring
    rw [this] at hB
    linarith
  rw [prod_split g0 g1 hg0p hg1p r, ← hPdef]
  have e : ((g0 * g1) ^ (r * (r - 1) / 2) * P) ^ f =
      P ^ f * (g0 * g1) ^ (f * (r * (r - 1) / 2)) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (r * (r - 1) / 2) f,
      mul_comm ((g0 * g1) ^ (f * (r * (r - 1) / 2)))]
  rw [e]
  exact mul_le_mul_of_nonneg_right hc (by positivity)
end GeoProdPow
