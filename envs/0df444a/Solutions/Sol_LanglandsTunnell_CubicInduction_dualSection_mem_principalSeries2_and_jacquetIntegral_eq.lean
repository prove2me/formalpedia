-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.dualSection_mem_principalSeries2_and_jacquetIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b8d146aa-8c0f-55c6-81cb-040384af4b3e

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

namespace SlJDS

open AutomorphicForm

variable (p : HeightOneSpectrum (𝓞 ℚ))
  (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
  (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

theorem upperUnipotent2_eq (x : p.adicCompletion ℚ) : upperUnipotent2 p x = unipotentGL2 x := Units.ext rfl

omit hw₀ in
theorem coe_inv_unipotentGL2 (x : p.adicCompletion ℚ) :
    (((unipotentGL2 x)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, -x; 0, 1] := rfl

omit hw₀ in
theorem coe_inv_diagonal2 (a : Fin 2 → (p.adicCompletion ℚ)ˣ) :
    (((diagonal2 p a)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      Matrix.diagonal fun i => (((a i)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := rfl

include hw₀

theorem w0_mul_w0 : w₀ * w₀ = 1 := by
  apply Units.ext
  rw [Units.val_mul, hw₀, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w0_inv : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right (w0_mul_w0 p w₀ hw₀)

theorem transposeInvN_w0 : transposeInvN (Fin 2) w₀ = w₀ := by
  apply Units.ext
  rw [coe_transposeInvN, w0_inv p w₀ hw₀, hw₀]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem w0_mul_transposeInvN_unipotent (x : p.adicCompletion ℚ) :
    w₀ * transposeInvN (Fin 2) (unipotentGL2 x) = unipotentGL2 (-x) * w₀ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, coe_inv_unipotentGL2, hw₀, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem transposeInvN_unipotent (y : p.adicCompletion ℚ) :
    transposeInvN (Fin 2) (unipotentGL2 y) = w₀ * unipotentGL2 (-y) * w₀ := by
  have h := w0_mul_transposeInvN_unipotent p w₀ hw₀ y
  have h2 := w0_mul_w0 p w₀ hw₀
  calc transposeInvN (Fin 2) (unipotentGL2 y) = (w₀ * w₀) * transposeInvN (Fin 2) (unipotentGL2 y) := by
        rw [h2, one_mul]
    _ = w₀ * (w₀ * transposeInvN (Fin 2) (unipotentGL2 y)) := by rw [mul_assoc]
    _ = w₀ * unipotentGL2 (-y) * w₀ := by rw [h, mul_assoc]

theorem w0_mul_transposeInvN_diagonal2 (a : Fin 2 → (p.adicCompletion ℚ)ˣ) :
    w₀ * transposeInvN (Fin 2) (diagonal2 p a) = diagonal2 p ![(a 1)⁻¹, (a 0)⁻¹] * w₀ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, coe_inv_diagonal2, hw₀, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem w0_mul_transposeInvN_word (y : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    w₀ * transposeInvN (Fin 2) (w₀ * unipotentGL2 y * g) =
      w₀ * unipotentGL2 (-y) * (w₀ * transposeInvN (Fin 2) g) := by
  rw [transposeInvN_mul, transposeInvN_mul, transposeInvN_w0 p w₀ hw₀, transposeInvN_unipotent p w₀ hw₀]
  have h2 := w0_mul_w0 p w₀ hw₀
  calc w₀ * (w₀ * (w₀ * unipotentGL2 (-y) * w₀) * transposeInvN (Fin 2) g)
        = (w₀ * w₀) * (w₀ * unipotentGL2 (-y) * w₀) * transposeInvN (Fin 2) g := by simp only [mul_assoc]
    _ = w₀ * unipotentGL2 (-y) * (w₀ * transposeInvN (Fin 2) g) := by rw [h2, one_mul]; simp only [mul_assoc]

omit hw₀ in
theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : GL (Fin 2) (p.adicCompletion ℚ) → _) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((transposeInvN (Fin 2) g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    simp only [coe_transposeInvN]
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (((transposeInvN (Fin 2) g)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    simp only [coe_inv_transposeInvN]
    exact Units.continuous_val.matrix_transpose

theorem torusChar2_dual (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ) :
    torusChar2 p χ ![(a 1)⁻¹, (a 0)⁻¹] = torusChar2 p ![(χ 1)⁻¹, (χ 0)⁻¹] a := by
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    map_inv, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  ring

omit hw₀ in
theorem halfModulus2_dual (a : Fin 2 → (p.adicCompletion ℚ)ˣ) :
    halfModulus2 p ![(a 1)⁻¹, (a 0)⁻¹] = halfModulus2 p a := by
  simp only [halfModulus2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.val_inv_eq_inv_val,
    norm_inv, inv_div_inv]

end SlJDS

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    (fun g : GL (Fin 2) (p.adicCompletion ℚ) => f (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) ∈
        principalSeries2 p ![(χ 1)⁻¹, (χ 0)⁻¹] ∧
    (letI := localBorel ℚ p
     ∀ (θ : AddChar (p.adicCompletion ℚ) ℂ) (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
       (g : GL (Fin 2) (p.adicCompletion ℚ)),
       (Integrable (fun y : p.adicCompletion ℚ =>
            f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (w₀ * AutomorphicForm.unipotentGL2 y * g)) * θ⁻¹ y) ν ↔
          Integrable (fun y : p.adicCompletion ℚ =>
            f (w₀ * AutomorphicForm.unipotentGL2 y * (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) * θ y) ν) ∧
       ∫ y, f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (w₀ * AutomorphicForm.unipotentGL2 y * g)) * θ⁻¹ y ∂ν =
         ∫ y, f (w₀ * AutomorphicForm.unipotentGL2 y * (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) * θ y ∂ν) := by
  obtain ⟨hlc, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  refine ⟨?_, ?_⟩
  · refine mem_principalSeries2_iff.mpr ⟨?_, fun x g => ?_, fun a g => ?_⟩
    · exact hlc.comp_continuous (continuous_const.mul (SlJDS.continuous_transposeInvN p))
    · show f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (upperUnipotent2 p x * g)) =
        f (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)
      rw [AutomorphicForm.transposeInvN_mul, ← mul_assoc, SlJDS.upperUnipotent2_eq,
        SlJDS.w0_mul_transposeInvN_unipotent p w₀ hw₀, mul_assoc, ← SlJDS.upperUnipotent2_eq, hN]
    · show f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (diagonal2 p a * g)) =
        torusChar2 p ![(χ 1)⁻¹, (χ 0)⁻¹] a * halfModulus2 p a * f (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)
      rw [AutomorphicForm.transposeInvN_mul, ← mul_assoc, SlJDS.w0_mul_transposeInvN_diagonal2 p w₀ hw₀, mul_assoc, hT,
        SlJDS.torusChar2_dual p w₀ hw₀, SlJDS.halfModulus2_dual]
  · letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
    intro θ ν _ g
    set G : p.adicCompletion ℚ → ℂ := fun y =>
      f (w₀ * AutomorphicForm.unipotentGL2 y * (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) * θ y with hG
    have hfun : (fun y : p.adicCompletion ℚ =>
        f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (w₀ * AutomorphicForm.unipotentGL2 y * g)) * θ⁻¹ y) =
        fun y => G (-y) := by
      funext y
      simp only [hG, AddChar.inv_apply, SlJDS.w0_mul_transposeInvN_word p w₀ hw₀]
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact ⟨fun h => by simpa using h.comp_neg, fun h => h.comp_neg⟩
    · rw [hfun]
      exact integral_neg_eq_self G ν

end S_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq (solution)
