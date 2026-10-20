-- Prove2me | solution 2 for OAI.Cotype.exists_complex_shift_inverse_of_power_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:59:16.548987+00:00
-- url     : https://prove2.me/submissions/dc43d2ae-743f-4f09-a667-0f10066f0fe4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ComplexPowerGapInverse.lean:L11-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_complex_shift_inverse_of_power_gap. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_Cotype_exists_powerGapInverse

-- ---- from OAI.Analysis.Cotype.ComplexPowerGapInverse ----
namespace OAI

noncomputable section
namespace Cotype

theorem exists_complex_shift_inverse_of_power_gap {N : ℕ} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    (T : A) (hT : ‖T‖ ≤ 1) (hTN : ‖(1-T)^N‖ ≤ C)
    (β : ℂ) (hβ : ρ ≤ ‖β‖) :
    ∃ U : Aˣ, (U : A) = (β-1) • (1 : A) + T ∧
      ‖(↑U⁻¹ : A)‖ ≤ powerGapInverseBound N (2/ρ) (C/ρ^N) / ‖β‖ := by
  have hβpos : 0 < ‖β‖ := hρ.trans_le hβ
  have hβne : β ≠ 0 := norm_pos_iff.mp hβpos
  let H : A := β⁻¹ • (1-T)
  have hb : 0 ≤ 2/ρ := by positivity
  have hq : C/ρ^N < 1 := (div_lt_one (pow_pos hρ N)).mpr hgap
  have hH : ‖H‖ ≤ 2/ρ := by
    dsimp [H]
    rw [norm_smul, norm_inv]
    calc
      _ ≤ ‖β‖⁻¹ * (‖(1 : A)‖ + ‖T‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ ρ⁻¹ * 2 := mul_le_mul (inv_anti₀ hρ hβ)
        (by rw [norm_one]; linarith) (by positivity) (by positivity)
      _ = 2/ρ := by ring
  have hHN : ‖H^N‖ ≤ C/ρ^N := by
    dsimp [H]
    rw [smul_pow, norm_smul, norm_pow, norm_inv]
    calc
      _ ≤ (‖β‖⁻¹)^N * C := mul_le_mul_of_nonneg_left hTN (by positivity)
      _ ≤ (ρ⁻¹)^N * C := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (inv_anti₀ hρ hβ) N) hC
      _ = C/ρ^N := by rw [inv_pow, div_eq_mul_inv, mul_comm]
  obtain ⟨V, hV, hnormV⟩ := exists_powerGapInverse hb hq H hH hHN
  have hv1 : (V : A)*(↑V⁻¹ : A) = 1 := V.val_inv
  have hv2 : (↑V⁻¹ : A)*(V : A) = 1 := V.inv_val
  let U : Aˣ :=
    ⟨β • (V : A), β⁻¹ • (↑V⁻¹ : A), by
      rw [smul_mul_assoc, mul_smul_comm, hv1, smul_smul,
        mul_inv_cancel₀ hβne, one_smul], by
      rw [smul_mul_assoc, mul_smul_comm, hv2, smul_smul,
        inv_mul_cancel₀ hβne, one_smul]⟩
  refine ⟨U, ?_, ?_⟩
  · change β • (V : A) = _
    rw [hV]
    dsimp [H]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hβne, one_smul]
    module
  · change ‖β⁻¹ • (↑V⁻¹ : A)‖ ≤ _
    rw [norm_smul, norm_inv]
    exact (mul_le_mul_of_nonneg_left hnormV (by positivity)).trans_eq
      (by simp only [div_eq_mul_inv]; ring)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.exists_complex_shift_inverse_of_power_gap := @_root_.OAI.Cotype.exists_complex_shift_inverse_of_power_gap
