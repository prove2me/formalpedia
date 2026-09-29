-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.conj_transposeInvN_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f4c08caa-0f49-51be-a5fc-2671f33cbfb6

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Ws48PS2

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem coe_inv_upperUnipotent2 (x : F) :
    (((upperUnipotent2 p x)⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F) = !![1, -x; 0, 1] := rfl

theorem coe_inv_diagonal2 (a : Fin 2 → Fˣ) :
    (((diagonal2 p a)⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F) := rfl

section W

theorem w_mul_w (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : w₀p * w₀p = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, hw₀p, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w_inv (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : w₀p⁻¹ = w₀p :=
  inv_eq_of_mul_eq_one_right (w_mul_w w₀p hw₀p)

theorem antidiagonal2_eq_w (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : antidiagonal2 p = w₀p :=
  Units.ext (by rw [antidiagonal2_coe, hw₀p])

theorem transposeInvN_w (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : transposeInvN (Fin 2) w₀p = w₀p := by
  refine Units.ext ?_
  rw [coe_transposeInvN, w_inv w₀p hw₀p, hw₀p]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem w_mul_transposeInvN_upperUnipotent2 (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (x : F) :
    w₀p * transposeInvN (Fin 2) (upperUnipotent2 p x) = upperUnipotent2 p (-x) * w₀p := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_transposeInvN, coe_inv_upperUnipotent2, upperUnipotent2_coe, hw₀p]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem transposeInvN_upperUnipotent2 (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (x : F) :
    transposeInvN (Fin 2) (upperUnipotent2 p x) = w₀p * upperUnipotent2 p (-x) * w₀p := by
  have h := w_mul_transposeInvN_upperUnipotent2 w₀p hw₀p x
  calc transposeInvN (Fin 2) (upperUnipotent2 p x) = w₀p * (w₀p * transposeInvN (Fin 2) (upperUnipotent2 p x)) := by
        rw [← mul_assoc, w_mul_w w₀p hw₀p, one_mul]
    _ = _ := by rw [h, mul_assoc]

theorem w_mul_transposeInvN_diagonal2 (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (a : Fin 2 → Fˣ) :
    w₀p * transposeInvN (Fin 2) (diagonal2 p a) = diagonal2 p ![(a 1)⁻¹, (a 0)⁻¹] * w₀p := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_transposeInvN, coe_inv_diagonal2, diagonal2_coe, hw₀p, Matrix.diagonal_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

theorem w_mul_upperUnipotent2_mul_diag (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (x : F) :
    w₀p * upperUnipotent2 p x * diagonal2 p ![1, -1] = diagonal2 p ![-1, 1] * (w₀p * upperUnipotent2 p (-x)) := by
  refine Units.ext ?_
  simp only [Units.val_mul, upperUnipotent2_coe, diagonal2_coe, hw₀p]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

end W

theorem continuous_transposeInvN : Continuous (fun h : G₂ => transposeInvN (Fin 2) h) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun h : G₂ => ((transposeInvN (Fin 2) h : G₂) : Matrix (Fin 2) (Fin 2) F)
    simp only [coe_transposeInvN]
    exact (Units.continuous_coe_inv).matrix_transpose
  · show Continuous fun h : G₂ => (((transposeInvN (Fin 2) h)⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F)
    simp only [coe_inv_transposeInvN]
    exact Units.continuous_val.matrix_transpose

theorem torusChar2_dual (μ : Fin 2 → (Fˣ →* ℂˣ)) (a : Fin 2 → Fˣ) :
    torusChar2 p μ ![(a 1)⁻¹, (a 0)⁻¹] = torusChar2 p ![(μ 1)⁻¹, (μ 0)⁻¹] a := by
  simp [torusChar2, Fin.prod_univ_two, mul_comm]

theorem halfModulus2_dual (a : Fin 2 → Fˣ) :
    halfModulus2 p ![(a 1)⁻¹, (a 0)⁻¹] = halfModulus2 p a := by
  simp only [halfModulus2, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_inv_eq_inv_val,
    norm_inv]
  rw [inv_div_inv]

theorem dual_mem (μ : Fin 2 → (Fˣ →* ℂˣ)) (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) :
    (fun h : G₂ => φ (w₀p * transposeInvN (Fin 2) h * w₀p)) ∈ principalSeries2 p ![(μ 1)⁻¹, (μ 0)⁻¹] := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries2_iff.mp hφ
  refine mem_principalSeries2_iff.mpr ⟨?_, fun x g => ?_, fun a g => ?_⟩
  · exact hlc.comp_continuous ((continuous_const.mul continuous_transposeInvN).mul continuous_const)
  · show φ (w₀p * transposeInvN (Fin 2) (upperUnipotent2 p x * g) * w₀p) = φ (w₀p * transposeInvN (Fin 2) g * w₀p)
    rw [transposeInvN_mul, ← mul_assoc w₀p, w_mul_transposeInvN_upperUnipotent2 w₀p hw₀p, mul_assoc (upperUnipotent2 p (-x)),
      mul_assoc (upperUnipotent2 p (-x)), hn]
  · show φ (w₀p * transposeInvN (Fin 2) (diagonal2 p a * g) * w₀p) =
      torusChar2 p ![(μ 1)⁻¹, (μ 0)⁻¹] a * halfModulus2 p a * φ (w₀p * transposeInvN (Fin 2) g * w₀p)
    rw [transposeInvN_mul, ← mul_assoc w₀p, w_mul_transposeInvN_diagonal2 w₀p hw₀p, mul_assoc (diagonal2 p _),
      mul_assoc (diagonal2 p _), ht, torusChar2_dual, halfModulus2_dual]

end Ws48PS2

end

namespace Ws48PS2

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem torusChar2_halfModulus2_neg_one_one (μ : Fin 2 → (Fˣ →* ℂˣ)) :
    torusChar2 p ![(μ 1)⁻¹, (μ 0)⁻¹] ![-1, 1] * halfModulus2 p ![-1, 1] = (((μ 1 (-1) : ℂˣ) : ℂ))⁻¹ := by
  simp [torusChar2, halfModulus2, Fin.prod_univ_two]

theorem dual_apply_diag (μ : Fin 2 → (Fˣ →* ℂˣ)) (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (Z : G₂) :
    φ (w₀p * transposeInvN (Fin 2) (diagonal2 p ![-1, 1] * Z) * w₀p) =
      (((μ 1 (-1) : ℂˣ) : ℂ))⁻¹ * φ (w₀p * transposeInvN (Fin 2) Z * w₀p) := by
  have ht := (mem_principalSeries2_iff.mp (dual_mem μ φ hφ w₀p hw₀p)).2.2 ![-1, 1] Z
  rw [ht, torusChar2_halfModulus2_neg_one_one]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem dual_integral (μ : Fin 2 → (Fˣ →* ℂˣ)) (φ : G₂ → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : G₂) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (g : G₂) :
    (∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) =
      ((μ 1 (-1) : ℂˣ) : ℂ) *
        ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
          φ (w₀p * transposeInvN (Fin 2) (antidiagonal2 p * upperUnipotent2 p x * (diagonal2 p ![1, -1] * g * w₀p)) * w₀p)
          ∂(selfDualHaarAt ℚ p) := by
  have hww : ∀ X : G₂, w₀p * (w₀p * X) = X := fun X => by
    rw [← mul_assoc, w_mul_w w₀p hw₀p, one_mul]

  have hL : ∀ x : F, φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) =
      φ (w₀p * transposeInvN (Fin 2) (w₀p * upperUnipotent2 p (-x) * g * w₀p) * w₀p) := by
    intro x
    rw [transposeInvN_mul, transposeInvN_mul, transposeInvN_mul, transposeInvN_w w₀p hw₀p,
      transposeInvN_upperUnipotent2 w₀p hw₀p (-x), neg_neg, antidiagonal2_eq_w w₀p hw₀p]
    simp only [mul_assoc, hww, w_mul_w w₀p hw₀p, mul_one]

  have hR : ∀ x : F, φ (w₀p * transposeInvN (Fin 2) (antidiagonal2 p * upperUnipotent2 p x * (diagonal2 p ![1, -1] * g * w₀p)) * w₀p) =
      (((μ 1 (-1) : ℂˣ) : ℂ))⁻¹ * φ (w₀p * transposeInvN (Fin 2) (w₀p * upperUnipotent2 p (-x) * g * w₀p) * w₀p) := by
    intro x
    have hm : antidiagonal2 p * upperUnipotent2 p x * (diagonal2 p ![1, -1] * g * w₀p) =
        diagonal2 p ![-1, 1] * (w₀p * upperUnipotent2 p (-x) * g * w₀p) := by
      rw [antidiagonal2_eq_w w₀p hw₀p, ← mul_assoc, ← mul_assoc, w_mul_upperUnipotent2_mul_diag w₀p hw₀p]
      simp only [mul_assoc]
    rw [hm, dual_apply_diag μ φ hφ w₀p hw₀p]
  simp_rw [hL, hR]
  have hc : (((μ 1 (-1) : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
  have hfun : (fun x : F => NumberField.StandardAddChar.psiLocal ℚ p x *
      ((((μ 1 (-1) : ℂˣ) : ℂ))⁻¹ * φ (w₀p * transposeInvN (Fin 2) (w₀p * upperUnipotent2 p (-x) * g * w₀p) * w₀p))) =
      fun x : F => (((μ 1 (-1) : ℂˣ) : ℂ))⁻¹ * (NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (w₀p * transposeInvN (Fin 2) (w₀p * upperUnipotent2 p (-x) * g * w₀p) * w₀p)) := by
    funext x; ring
  rw [hfun, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

end Ws48PS2

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    (fun h : GL (Fin 2) (p.adicCompletion ℚ) => φ (w₀p * transposeInvN (Fin 2) h * w₀p)) ∈
      principalSeries2 p ![(μ 1)⁻¹, (μ 0)⁻¹] :=
  Ws48PS2.dual_mem μ φ hφ w₀p hw₀p

end S_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2 (solution)
