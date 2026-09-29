-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/22907a9e-b93d-5add-a555-ce6f9fa87ea9

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
open scoped nonZeroDivisors

namespace MulDualUnipotentEngine

open Matrix

section MatrixIdentities

variable {K : Type*} [Field K]

theorem unipotent_val (x : K) :
    ((UnramifiedWhittaker.unipotent x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] :=
  rfl

theorem unipotent_mul_unipotent (x y : K) :
    UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.unipotent y =
      UnramifiedWhittaker.unipotent (x + y) := by
  refine Units.ext ?_
  rw [Units.val_mul, unipotent_val, unipotent_val, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_zero : (UnramifiedWhittaker.unipotent (0 : K)) = 1 := by
  refine Units.ext ?_
  rw [unipotent_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_inv (x : K) :
    (UnramifiedWhittaker.unipotent x)⁻¹ = UnramifiedWhittaker.unipotent (-x) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [unipotent_mul_unipotent, add_neg_cancel, unipotent_zero]

theorem transposeInvN_unipotent_val (x : K) :
    ((AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = !![1, 0; -x, 1] := by
  rw [AutomorphicForm.coe_transposeInvN, unipotent_inv, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem gl2Weyl_mul_transposeInvN_unipotent (x : K) :
    (AutomorphicForm.gl2Weyl : GL (Fin 2) K) *
        AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x) =
      UnramifiedWhittaker.unipotent (-x) * AutomorphicForm.gl2Weyl := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, transposeInvN_unipotent_val, unipotent_val,
    AutomorphicForm.gl2Weyl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem gl2Weyl_mul_transposeInvN_unipotent_mul (x : K) (h : GL (Fin 2) K) :
    (AutomorphicForm.gl2Weyl : GL (Fin 2) K) *
        AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x * h) =
      UnramifiedWhittaker.unipotent (-x) *
        ((AutomorphicForm.gl2Weyl : GL (Fin 2) K) * AutomorphicForm.transposeInvN (Fin 2) h) := by
  rw [AutomorphicForm.transposeInvN_mul, ← mul_assoc, gl2Weyl_mul_transposeInvN_unipotent, mul_assoc]

end MatrixIdentities

section Embedding

theorem iotaGL_unipotent {K : Type*} [Field K] (x : K) :
    LanglandsTunnell.CubicInduction.iotaGL (UnramifiedWhittaker.unipotent x) =
      LanglandsTunnell.CubicInduction.upperUnipotent3 x 0 0 := by
  refine Units.ext ?_
  rw [LanglandsTunnell.CubicInduction.coe_iotaGL, unipotent_val,
    LanglandsTunnell.CubicInduction.upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.embedMat2]

end Embedding

end MulDualUnipotentEngine

open MulDualUnipotentEngine LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (F : LocalGL3 v → ℂ) (hF : IsGL3PsiWhittakerFn ψv⁻¹ F)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (x : v.adicCompletion ℚ) (X : LocalGL3 v) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    F (iotaGL (UnramifiedWhittaker.unipotent x) * X) *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x * h)) =
      F X *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) h) := by

  have hFx : F (iotaGL (UnramifiedWhittaker.unipotent x) * X) =
      NumberField.StandardAddChar.psiLocal ℚ v x * F X := by
    have h1 := hF x 0 0 X
    rw [iotaGL_unipotent]
    rw [h1, add_zero, hψinv, inv_inv]

  have hWx : W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
        AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x * h)) =
      NumberField.StandardAddChar.psiLocal ℚ v (-x) *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) h) := by
    rw [gl2Weyl_mul_transposeInvN_unipotent_mul, hW₂ψ]

  have hcancel : NumberField.StandardAddChar.psiLocal ℚ v x *
      NumberField.StandardAddChar.psiLocal ℚ v (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [hFx, hWx]
  calc NumberField.StandardAddChar.psiLocal ℚ v x * F X *
        (NumberField.StandardAddChar.psiLocal ℚ v (-x) *
          W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
            AutomorphicForm.transposeInvN (Fin 2) h))
      = (NumberField.StandardAddChar.psiLocal ℚ v x *
          NumberField.StandardAddChar.psiLocal ℚ v (-x)) *
          (F X * W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
            AutomorphicForm.transposeInvN (Fin 2) h)) := by ring
    _ = F X * W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
            AutomorphicForm.transposeInvN (Fin 2) h) := by rw [hcancel, one_mul]

end S_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent (solution)
