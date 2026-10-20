-- Prove2me | solution 1 for OAI.Cotype.exists_complex_shift_inverse_of_power_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:24:05.194496+00:00
-- url     : https://prove2.me/submissions/2727dab2-4448-41e1-b5ac-16f1d7380a51

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
theorem h50c_pgi {N : ℕ} {b q : ℝ}
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

theorem solution {N : ℕ} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    (T : A) (hT : ‖T‖ ≤ 1) (hTN : ‖(1-T)^N‖ ≤ C)
    (β : ℂ) (hβ : ρ ≤ ‖β‖) :
    ∃ U : Aˣ, (U : A) = (β-1) • (1 : A) + T ∧
      ‖(↑U⁻¹ : A)‖ ≤ powerGapInverseBound N (2/ρ) (C/ρ^N) / ‖β‖ := by
  have hβ0 : (β : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; linarith
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  set H : A := β⁻¹ • (1 - T) with hHdef
  have h1T : ‖1 - T‖ ≤ 2 := by
    calc ‖1 - T‖ ≤ ‖(1:A)‖ + ‖T‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hH : ‖H‖ ≤ 2/ρ := by
    rw [hHdef, norm_smul, norm_inv]
    calc ‖β‖⁻¹ * ‖1 - T‖ ≤ ρ⁻¹ * 2 := mul_le_mul (inv_anti₀ hρ hβ) h1T (norm_nonneg _) (inv_nonneg.2 hρ.le)
      _ = 2/ρ := by ring
  have hHN : ‖H^N‖ ≤ C/ρ^N := by
    rw [hHdef, smul_pow, norm_smul, norm_pow, norm_inv, inv_pow]
    have hρN : 0 < ρ^N := pow_pos hρ N
    calc (‖β‖^N)⁻¹ * ‖(1 - T)^N‖ ≤ (ρ^N)⁻¹ * C :=
          mul_le_mul (inv_anti₀ hρN (pow_le_pow_left₀ hρ.le hβ N)) hTN (norm_nonneg _) (inv_nonneg.2 hρN.le)
      _ = C/ρ^N := by ring
  have hq : C/ρ^N < 1 := by rw [div_lt_one (pow_pos hρ N)]; exact hgap
  obtain ⟨V, hV, hVb⟩ := h50c_pgi (by positivity) hq H hH hHN
  have hrel : β • (1 - H) = (β-1) • (1 : A) + T := by
    rw [hHdef, smul_sub, smul_smul, mul_inv_cancel₀ hβ0, one_smul, sub_smul, one_smul]; abel
  refine ⟨⟨β • (V : A), β⁻¹ • ((V⁻¹ : Aˣ) : A), ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hβ0, Units.mul_inv, one_smul]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hβ0, Units.inv_mul, one_smul]
  · show β • (V : A) = _
    rw [hV, hrel]
  · show ‖β⁻¹ • ((V⁻¹ : Aˣ) : A)‖ ≤ _
    rw [norm_smul, norm_inv, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hVb (inv_nonneg.2 hβpos.le)

