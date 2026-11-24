-- Prove2me | solution 1 for GlobalTheory.SW.norm_det_denom_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:53:30.355736+00:00
-- url     : https://prove2.me/submissions/edb952bb-e219-4dd9-8087-0cdd3cfcb2c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Theorems.Thm_GlobalTheory_SW_norm_det_le_add_posSemidef
import Theorems.Thm_GlobalTheory_SW_posSemidef_sub_mul_conjTranspose
import Theorems.Thm_GlobalTheory_SW_denom_mul_conjTranspose
import Theorems.Thm_GlobalTheory_SW_norm_det_mul_conjTranspose
import Theorems.Thm_GlobalTheory_SW_imH_add_I_smul
import Theorems.Thm_GlobalTheory_SW_norm_det_denom_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
variable {N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution :
    ∀ (N : ℕ) (δ B : ℝ), 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C D Z : Matrix (Fin N) (Fin N) ℂ, (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → (∀ a b, ‖(Z + Zᴴ) a b‖ ≤ B) → c * ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ≤ ‖(C * Z + D).det‖ ∧ ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 = (C * Cᴴ + D * Dᴴ).det.re := by
  intro N δ B hδ
  set K : ℝ := (N : ℝ) ^ 2 * (B / 2) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := δ ^ 2 / (2 * δ ^ 2 + 1 + 2 * K) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : 0 ≤ 1 - 2 * c := by
    rw [hc, sub_nonneg, ← mul_div_assoc, div_le_one (by positivity)]
    linarith
  have hc2 : 0 ≤ δ ^ 2 - c - 2 * c * K := by
    have : c * (2 * δ ^ 2 + 1 + 2 * K) = δ ^ 2 := by rw [hc]; field_simp
    nlinarith [mul_pos hc0 (pow_pos hδ 2)]
  refine ⟨Real.sqrt (c ^ N), by positivity, fun C D Z h hp hZ hB => ?_⟩
  have hG : (C * Cᴴ + D * Dᴴ).det =
      ((‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 : ℝ) : ℂ) := by
    have := denom_mul_conjTranspose C D 0 h isHermitian_zero 1
    rw [← norm_det_mul_conjTranspose]
    simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at this
    rw [this, add_comm]
  refine ⟨?_, by rw [hG, ofReal_re]⟩
  set X : Matrix (Fin N) (Fin N) ℂ := (2⁻¹ : ℂ) • (Z + Zᴴ) with hXdef
  have hX : X.IsHermitian := by
    simp [hXdef, IsHermitian, add_comm]
  have hXB : ∀ a b, ‖X a b‖ ≤ B / 2 := by
    intro a b
    have := hB a b
    rw [hXdef, Matrix.smul_apply, norm_smul]
    simp only [norm_inv, Complex.norm_ofNat]
    linarith
  have hone : ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hδ)
  have him : imH (X + (I * δ) • 1) = (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    rw [mul_smul, imH_add_I_smul _ _ hone.1, imH, hX.eq]
    simp
  have hZe : X + (I * δ) • 1 + I • (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = Z := by
    have h2 : I * (2 * I)⁻¹ = 2⁻¹ := by field_simp
    rw [smul_sub, imH, smul_smul, smul_smul, h2, hXdef]
    module
  have hm := (norm_det_denom_mono N C D (X + (I * δ) • 1) _ h hp (by rwa [him]) hZ).2
  rw [hZe] at hm
  refine le_trans ?_ hm
  have hP : ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)).PosSemidef := by
    refine (((posSemidef_self_mul_conjTranspose _).smul ?_).add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)).add
      (((posSemidef_sub_mul_conjTranspose X _ hXB).mul_mul_conjTranspose_same C).smul ?_) |>.add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)
    · exact Complex.zero_le_real.2 hc1
    · exact Complex.zero_le_real.2 hc2
    · exact Complex.zero_le_real.2 (by positivity)
    · exact Complex.zero_le_real.2 hc0.le
  have hd := norm_det_le_add_posSemidef _ _ (hp.smul (Complex.zero_lt_real.2 hc0)) hP
  have he : (c : ℂ) • (C * Cᴴ + D * Dᴴ) + ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)) =
      (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ := by
    rw [denom_mul_conjTranspose C D X h hX]
    push_cast
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    module
  rw [he, norm_det_mul_conjTranspose, det_smul, hG, ← ofReal_pow, ← ofReal_mul, norm_real,
    norm_real, Fintype.card_fin, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hd
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity)]
end GlobalTheory.SW
