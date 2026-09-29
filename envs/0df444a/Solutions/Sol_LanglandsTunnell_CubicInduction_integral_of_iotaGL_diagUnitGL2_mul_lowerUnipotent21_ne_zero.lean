-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4a35170c-49cd-5510-b28a-93eb6cac0775

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero

set_option autoImplicit false

open IsDedekindDomain Matrix NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.integral_of_iotaGL_diagUnits2_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 lowerUnipotent21_coe IsGL3PsiWhittakerFn upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagUnits2 coe_diagUnits2 integral_of_iotaGL_diagUnits2_ne_zero"
namespace LowerUnipotentSupportQ
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

local notation "Kv" => v.adicCompletion K

theorem upperUnipotent3_entry_le (x y z : Kv) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hz : Valued.v z ≤ 1) (i j : Fin 3) :
    Valued.v ((upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) Kv) i j) ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hx, hy, hz]

theorem upperUnipotent3_mem (x y z : Kv) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) (hz : Valued.v z ≤ 1) :
    upperUnipotent3 x y z ∈ localMaximalCompact3 R K v := by
  have hinv : ((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) Kv) = upperUnipotent3 (-x) (-y) (x * y - z) := by
    rw [inv_eq_iff_mul_eq_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring
  have hxy : Valued.v (x * y - z) ≤ 1 := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hz)
    rw [map_mul]
    calc Valued.v x * Valued.v y ≤ 1 * 1 := mul_le_mul' hx hy
      _ = 1 := one_mul _
  refine ⟨upperUnipotent3_entry_le v x y z hx hy hz, ?_⟩
  rw [hinv]
  exact upperUnipotent3_entry_le v (-x) (-y) (x * y - z) (by rwa [Valuation.map_neg])
    (by rwa [Valuation.map_neg]) hxy

noncomputable def kZero (x : Kvˣ) : GL (Fin 3) Kv where
  val := !![0, -1, 0; 1, ((x⁻¹ : Kvˣ) : Kv), 0; 0, 0, 1]
  inv := !![((x⁻¹ : Kvˣ) : Kv), 1, 0; -1, 0, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[scoped simp] theorem kZero_coe (x : Kvˣ) :
    ((kZero v x : GL (Fin 3) Kv) : Matrix (Fin 3) (Fin 3) Kv) = !![0, -1, 0; 1, ((x⁻¹ : Kvˣ) : Kv), 0; 0, 0, 1] :=
  rfl

@[scoped simp] theorem kZero_inv_coe (x : Kvˣ) :
    (((kZero v x)⁻¹ : GL (Fin 3) Kv) : Matrix (Fin 3) (Fin 3) Kv) = !![((x⁻¹ : Kvˣ) : Kv), 1, 0; -1, 0, 0; 0, 0, 1] :=
  rfl

theorem kZero_mem (x : Kvˣ) (hx : 1 ≤ Valued.v (x : Kv)) : kZero v x ∈ localMaximalCompact3 R K v := by
  have hxi : (Valued.v (x : Kv))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  refine ⟨?_, ?_⟩
  · intro i j
    rw [kZero_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hxi]
  · intro i j
    rw [kZero_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hxi]

theorem diag_mul_lowerUnipotent21 (a x : Kvˣ) :
    iotaGL (diagUnitGL2 a) * lowerUnipotent21 (x : Kv) =
      upperUnipotent3 ((a : Kv) * ((x⁻¹ : Kvˣ) : Kv)) 0 0 * iotaGL (diagUnits2 (a * x⁻¹) x) * kZero v x := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_iotaGL, lowerUnipotent21_coe, upperUnipotent3_coe, kZero_coe, coe_diagUnits2,
    coe_diagUnitGL2, embedMat2, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

end LanglandsTunnell.CubicInduction.LowerUnipotentSupportQ
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell.CubicInduction.LowerUnipotentSupportQ"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (hW0 : W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x) ≠ 0) :
    x ∈ v.adicCompletionIntegers ℚ := by
  by_contra hx

  have hx1 : 1 < Valued.v x :=
    lt_of_not_ge fun h => hx ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr h)
  have hx0 : x ≠ 0 := fun h => by
    rw [h, map_zero] at hx1
    exact not_lt_of_ge zero_le' hx1
  set xu : (v.adicCompletion ℚ)ˣ := Units.mk0 x hx0 with hxu
  have hxcoe : (xu : v.adicCompletion ℚ) = x := rfl

  have hinv : ∀ (g : LocalGL3 v) (p q r : v.adicCompletion ℚ),
      p ∈ v.adicCompletionIntegers ℚ → q ∈ v.adicCompletionIntegers ℚ → r ∈ v.adicCompletionIntegers ℚ →
        W (g * upperUnipotent3 p q r) = W g := by
    intro g p q r hp hq hr
    exact hK g _ (LowerUnipotentSupportQ.upperUnipotent3_mem v p q r
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hp)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hq)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hr))

  have hzero : W (iotaGL (diagUnits2 (a * xu⁻¹) xu)) = 0 := by
    by_contra h
    exact hx (hxcoe ▸
      (LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnits2_ne_zero v ψv hψ1 W hW hinv (a * xu⁻¹) xu h).2)

  apply hW0
  rw [← hxcoe, LowerUnipotentSupportQ.diag_mul_lowerUnipotent21 v a xu, mul_assoc, hW,
    hK _ _ (LowerUnipotentSupportQ.kZero_mem v xu (le_of_lt hx1)), hzero, mul_zero]

end S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero (solution)
