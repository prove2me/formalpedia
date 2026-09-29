-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn_of_mem_congruenceK1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d60e29a7-7f7a-5ea9-b199-b23bb45ef0d7

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn_of_mem_congruenceK1

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

open LanglandsTunnell.CubicInduction

namespace DominantTorusVanishing

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))

private theorem diag_entry_ne_zero (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (i : Fin 3) : d i ≠ 0 := by
  intro hi
  have hdet : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp t.isUnit |>.ne_zero
  apply hdet
  rw [ht, Matrix.det_diagonal]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

private theorem upperUnipotent3_left_mem_congruenceK1 (c : ℕ) {a : v.adicCompletion ℚ} (ha : Valued.v a ≤ 1) :
    upperUnipotent3 a 0 0 ∈ congruenceK1 (𝓞 ℚ) ℚ v c := by
  refine (mem_congruenceK1_iff (𝓞 ℚ) ℚ v).mpr ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [ha]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, ha]
  all_goals simp

private theorem upperUnipotent3_right_mem_congruenceK1 (c : ℕ) {b : v.adicCompletion ℚ} (hb : Valued.v b ≤ 1) :
    upperUnipotent3 0 b 0 ∈ congruenceK1 (𝓞 ℚ) ℚ v c := by
  refine (mem_congruenceK1_iff (𝓞 ℚ) ℚ v).mpr ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hb]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hb]
  all_goals simp

private theorem diag_mul_upperUnipotent3_left (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (h1 : d 1 ≠ 0)
    (a : v.adicCompletion ℚ) :
    t * upperUnipotent3 a 0 0 = upperUnipotent3 (d 0 * a / d 1) 0 0 * t := by
  ext i j
  simp only [Units.val_mul, ht, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]
  all_goals field_simp

private theorem diag_mul_upperUnipotent3_right (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (h2 : d 2 ≠ 0)
    (b : v.adicCompletion ℚ) :
    t * upperUnipotent3 0 b 0 = upperUnipotent3 0 (d 1 * b / d 2) 0 * t := by
  ext i j
  simp only [Units.val_mul, ht, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]
  all_goals field_simp

private theorem exists_param {x y x₀ : v.adicCompletion ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (h : Valued.v x < Valued.v y)
    (hx₀ : Valued.v x₀ ≤ 1) :
    ∃ a : v.adicCompletion ℚ, Valued.v a ≤ 1 ∧ y * a / x = (varpi v)⁻¹ * x₀ := by
  refine ⟨(varpi v)⁻¹ * x₀ * (x / y), ?_, ?_⟩
  · have hϖ : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
    by_cases hx0 : x₀ = 0
    · simp [hx0]
    have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    have hvx0 : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    rw [← WithZero.exp_log hvx, ← WithZero.exp_log hvy, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log hvx0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx₀
    rw [map_mul, map_mul, map_inv₀, map_div₀, hϖ, ← WithZero.exp_log hvx, ← WithZero.exp_log hvy,
      ← WithZero.exp_log hvx0, ← WithZero.exp_neg, ← WithZero.exp_sub, ← WithZero.exp_add, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have := varpi_ne_zero v
    field_simp

end DominantTorusVanishing

open DominantTorusVanishing in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (c : ℕ) (hW : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g, W (g * k) = W g) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (hd : Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)) :
    W t = 0 := by
  obtain ⟨x₀, hx₀, hψx₀⟩ := hψ1
  have hψ' : ∀ (x y : v.adicCompletion ℚ) (g : LocalGL3 v), W (upperUnipotent3 x y 0 * g) = ψv (x + y) * W g :=
    fun x y g => hψ x y 0 g
  have hne : (ψv ((varpi v)⁻¹ * x₀) : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hψx₀
  rcases hd with h01 | h12
  ·
    obtain ⟨a, ha, hconj⟩ :=
      exists_param v (diag_entry_ne_zero v t d ht 1) (diag_entry_ne_zero v t d ht 0) h01 hx₀
    have hinv := hW _ (upperUnipotent3_left_mem_congruenceK1 v c ha) t
    rw [diag_mul_upperUnipotent3_left v t d ht (diag_entry_ne_zero v t d ht 1), hψ', add_zero, hconj] at hinv

    have : ((ψv ((varpi v)⁻¹ * x₀) : ℂ) - 1) * W t = 0 := by rw [sub_mul, one_mul, hinv, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  ·
    obtain ⟨b, hb, hconj⟩ :=
      exists_param v (diag_entry_ne_zero v t d ht 2) (diag_entry_ne_zero v t d ht 1) h12 hx₀
    have hinv := hW _ (upperUnipotent3_right_mem_congruenceK1 v c hb) t
    rw [diag_mul_upperUnipotent3_right v t d ht (diag_entry_ne_zero v t d ht 2), hψ', zero_add, hconj] at hinv
    have : ((ψv ((varpi v)⁻¹ * x₀) : ℂ) - 1) * W t = 0 := by rw [sub_mul, one_mul, hinv, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne

end S_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn_of_mem_congruenceK1
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn_of_mem_congruenceK1 (solution)
