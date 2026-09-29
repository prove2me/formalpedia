-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/72f88de8-1cf8-5930-bed9-2eaa61964e98

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField
open LanglandsTunnell.CubicInduction

private theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · exact zero_le'
  · have h' : WithZero.log γ < 0 := by
      have h1 := h
      rw [← WithZero.exp_log hγ, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      exact h1
    calc γ = WithZero.exp (WithZero.log γ) := (WithZero.exp_log hγ).symm
      _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)

private theorem le_one_of_mul_le_right_of_ne_zero {a b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) (h : a * b ≤ b) : a ≤ 1 := by
  calc a = a * b * b⁻¹ := (mul_inv_cancel_right₀ hb a).symm
    _ ≤ b * b⁻¹ := mul_le_mul_left h _
    _ = 1 := mul_inv_cancel₀ hb

private theorem valued_le_valued_varpi_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a b : v.adicCompletion ℚ) (hb : b ≠ 0)
    (hab : Valued.v a < Valued.v b) : Valued.v a ≤ Valued.v (varpi v) * Valued.v b := by
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  have hq : Valued.v (a / b) < 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ (lt_of_le_of_ne zero_le' hb'.symm)).mpr hab
  have hq' : Valued.v (a / b) ≤ Valued.v (varpi v) := by
    rw [AdelicLevel.valued_uniformizerUnit]
    exact le_exp_neg_one_of_lt_one hq
  calc Valued.v a = Valued.v (a / b) * Valued.v b := by rw [← map_mul, div_mul_cancel₀ a hb]
    _ ≤ Valued.v (varpi v) * Valued.v b := mul_le_mul_left hq' _

private theorem valued_point_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (x₀ a b : v.adicCompletion ℚ) (hx₀ : Valued.v x₀ ≤ 1)
    (hb : b ≠ 0) (hab : Valued.v a < Valued.v b) : Valued.v ((varpi v)⁻¹ * x₀ * a / b) ≤ 1 := by
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  have hϖ : Valued.v (varpi v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (varpi_ne_zero v)
  refine le_one_of_mul_le_right_of_ne_zero hb' ?_
  calc Valued.v ((varpi v)⁻¹ * x₀ * a / b) * Valued.v b = Valued.v ((varpi v)⁻¹ * x₀) * Valued.v a := by
        rw [← map_mul, div_mul_cancel₀ _ hb, map_mul]
    _ ≤ Valued.v ((varpi v)⁻¹ * x₀) * (Valued.v (varpi v) * Valued.v b) :=
        mul_le_mul_right (valued_le_valued_varpi_mul v a b hb hab) _
    _ = Valued.v x₀ * Valued.v b := by
        rw [map_mul, map_inv₀, mul_mul_mul_comm, inv_mul_cancel₀ hϖ, one_mul]
    _ ≤ 1 * Valued.v b := mul_le_mul_left hx₀ _
    _ = Valued.v b := one_mul _

private theorem upperUnipotent3_first_mem (v : HeightOneSpectrum (𝓞 ℚ))
    (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) :
    upperUnipotent3 x 0 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hx]

private theorem upperUnipotent3_second_mem (v : HeightOneSpectrum (𝓞 ℚ))
    (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1) :
    upperUnipotent3 0 y 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hy]

private theorem mul_upperUnipotent3_first (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v)
    (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (x e : v.adicCompletion ℚ) (h : d 0 * x = e * d 1) :
    t * upperUnipotent3 x 0 0 = upperUnipotent3 e 0 0 * t := by
  ext1
  rw [Units.val_mul, Units.val_mul, ht, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, h]

private theorem mul_upperUnipotent3_second (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v)
    (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (y e : v.adicCompletion ℚ) (h : d 1 * y = e * d 2) :
    t * upperUnipotent3 0 y 0 = upperUnipotent3 0 e 0 * t := by
  ext1
  rw [Units.val_mul, Units.val_mul, ht, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, h]

private theorem eq_zero_of_self_eq_mul {c w : ℂ} (hc : c ≠ 1) (h : w = c * w) : w = 0 := by
  have h' : (c - 1) * w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hc)

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (hd : Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)) :
    W t = 0 := by
  obtain ⟨x₀, hx₀, hψx₀⟩ := hψ1
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [← ht]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit t)).ne_zero
  rw [Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  obtain ⟨⟨hd0, hd1⟩, -⟩ := mul_ne_zero_iff.mp hdet |>.imp_left mul_ne_zero_iff.mp
  rcases hd with h01 | h12
  · have hx := valued_point_le_one v x₀ (d 1) (d 0) hx₀ hd0 h01
    refine eq_zero_of_self_eq_mul hψx₀ ?_
    calc W t = W (t * upperUnipotent3 ((varpi v)⁻¹ * x₀ * d 1 / d 0) 0 0) :=
          (hW t _ (upperUnipotent3_first_mem v _ hx)).symm
      _ = W (upperUnipotent3 ((varpi v)⁻¹ * x₀) 0 0 * t) := by
          rw [mul_upperUnipotent3_first v t d ht ((varpi v)⁻¹ * x₀ * d 1 / d 0) ((varpi v)⁻¹ * x₀)
            (by rw [mul_comm]; exact div_mul_cancel₀ _ hd0)]
      _ = ψv ((varpi v)⁻¹ * x₀) * W t := by rw [hψ, add_zero]
  · have hx := valued_point_le_one v x₀ (d 2) (d 1) hx₀ hd1 h12
    refine eq_zero_of_self_eq_mul hψx₀ ?_
    calc W t = W (t * upperUnipotent3 0 ((varpi v)⁻¹ * x₀ * d 2 / d 1) 0) :=
          (hW t _ (upperUnipotent3_second_mem v _ hx)).symm
      _ = W (upperUnipotent3 0 ((varpi v)⁻¹ * x₀) 0 * t) := by
          rw [mul_upperUnipotent3_second v t d ht ((varpi v)⁻¹ * x₀ * d 2 / d 1) ((varpi v)⁻¹ * x₀)
            (by rw [mul_comm]; exact div_mul_cancel₀ _ hd1)]
      _ = ψv ((varpi v)⁻¹ * x₀) * W t := by rw [hψ, zero_add]

end S_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn (solution)
