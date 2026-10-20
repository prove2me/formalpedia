-- Prove2me | solution 1 for OAI.Cotype.exists_powerGapInverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:20:46.595364+00:00
-- url     : https://prove2.me/submissions/fd88dba6-72b4-4175-9921-ca4fd28bb3bb

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse

open OAI OAI.Cotype
open scoped BigOperators


theorem solution {N : ℕ} {b q : ℝ}
    (hb : 0 ≤ b) (hq : q < 1)
    {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]
    (H : R) (hH : ‖H‖ ≤ b) (hHN : ‖H^N‖ ≤ q) :
    ∃ U : Rˣ, (U : R) = 1-H ∧ ‖(↑U⁻¹ : R)‖ ≤ powerGapInverseBound N b q := by
  have hHN1 : ‖H^N‖ < 1 := lt_of_le_of_lt hHN hq
  let V : Rˣ := Units.oneSub (H^N) hHN1
  let S : R := ∑ k ∈ Finset.range N, H^k
  have hSl : S * (1 - H) = 1 - H^N := by
    simp only [S]; rw [Finset.sum_mul]
    simp only [mul_sub, mul_one, ← pow_succ]
    rw [Finset.sum_range_sub' (fun k => H^k)]; simp
  have hSr : (1 - H) * S = 1 - H^N := by
    simp only [S]; rw [Finset.mul_sum]
    simp only [sub_mul, one_mul, ← pow_succ']
    rw [Finset.sum_range_sub' (fun k => H^k)]; simp
  have hV : (V : R) = 1 - H^N := rfl
  have hHc : Commute (H^N) H := (Commute.refl H).pow_left N
  have hcomm : Commute (V : R) (1 - H) := by
    rw [hV]; exact (Commute.one_left (1-H)).sub_left ((Commute.one_right (H^N)).sub_right hHc)
  have hci : Commute ((V⁻¹ : Rˣ) : R) (1 - H) := hcomm.units_inv_left
  refine ⟨⟨1 - H, ((V⁻¹ : Rˣ) : R) * S, ?_, ?_⟩, rfl, ?_⟩
  · rw [← mul_assoc, ← hci.eq, mul_assoc, hSr, ← hV, Units.inv_mul]
  · rw [mul_assoc, hSl, ← hV, Units.inv_mul]
  · show ‖((V⁻¹ : Rˣ) : R) * S‖ ≤ _
    have h1 : ‖((V⁻¹ : Rˣ) : R)‖ ≤ (1 - q)⁻¹ := by
      have hb := tsum_geometric_le_of_norm_lt_one (H^N) hHN1
      have : ((V⁻¹ : Rˣ) : R) = ∑' n, (H^N)^n := rfl
      rw [this]
      have : (1 - ‖H^N‖)⁻¹ ≤ (1 - q)⁻¹ := by
        apply inv_anti₀ (by linarith) (by linarith)
      simp only [norm_one, sub_self, zero_add] at hb
      linarith
    have h2 : ‖S‖ ≤ ∑ k ∈ Finset.range N, b^k := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      exact (norm_pow_le H k).trans (pow_le_pow_left₀ (norm_nonneg _) hH k)
    have hq0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg (H^N)])
    rw [powerGapInverseBound, div_eq_mul_inv, mul_comm (∑ k ∈ Finset.range N, b^k)]
    exact (norm_mul_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) hq0)

