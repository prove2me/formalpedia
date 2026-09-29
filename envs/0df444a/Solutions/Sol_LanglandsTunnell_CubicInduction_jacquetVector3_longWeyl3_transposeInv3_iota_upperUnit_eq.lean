-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b1151edb-1a49-548b-b3f1-35b86da606c1

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

/-!

                                                              -/

namespace Ws23HLD2

open AutomorphicForm.StandardKernel

abbrev hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((archRealGLAt hR M : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl : v = default := Subsingleton.elim _ _
  show AutomorphicForm.archMatrixUpdate ℚ default ((glEquivOfRingEquiv (ringEquivRealOfIsReal hR).symm M :
    GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix _ _ _) i j default = _
  rw [AutomorphicForm.archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem realCoord_iotaR (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    realCoord (((archRealGLAt hR M : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      (M : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  rw [realCoord_apply, iotaR_fst]
  exact (ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply _

theorem realMat_iotaHat (M : GL (Fin 2) ℝ) :
    realMat (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt hR M))) =
      !![(M : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1, 0;
         (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1, 0;
         0, 0, 1] := by
  rw [realMat_eq]
  ext i j
  rw [Matrix.map_apply]
  change realCoord (embedMat2 ((archRealGLAt hR M : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = _
  fin_cases i <;> fin_cases j <;> simp [embedMat2, realCoord_iotaR] <;>
    first | exact map_zero realCoord | exact map_one realCoord

theorem realMat_transposeInv3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    realMat (transposeInv3 g) = Matrix.transpose ((realMat g)⁻¹) := by
  have h : ((transposeInv3 g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      Matrix.transpose ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) := rfl
  rw [realMat_eq, h, Matrix.transpose_map, ← realMat_eq, realMat_inv]

theorem realMat_longWeyl3 : realMat (longWeyl3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  rw [realMat_eq, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

end Ws23HLD2

open Ws23HLD2 AutomorphicForm.StandardKernel in
set_option linter.unusedVariables false in
theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    jacquetVector3 D u₃ a₃ a ψ S
        (longWeyl3 * transposeInv3 (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ
          (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
            (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne'))))) =
      ArchR.quasiChar (u₃ + 1) a₃ (-(a₁ * a₂)⁻¹) *
        ∫ e : Fin 2 → Fin 2 → ℝ,
          (∫ v : Fin 2 → ℝ,
              S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
                ψ (AutomorphicForm.StandardKernel.ofReal (-(v 1)))) *
            ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne a * (Matrix.of e)⁻¹) := by

  set M : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, a₂⁻¹, 0; a₁⁻¹, 0, 0] with hM
  have hdiag_inv : (!![a₁, 0, 0; 0, a₂, 0; (0 : ℝ), 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ = !![a₁⁻¹, 0, 0; 0, a₂⁻¹, 0; 0, 0, 1] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ha₁, ha₂.ne']
  have hR : realMat (longWeyl3 * transposeInv3 (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
        (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne'))))) = M := by
    rw [realMat_mul, realMat_longWeyl3, realMat_transposeInv3, realMat_iotaHat]
    simp only [AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero, AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one,
      AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero, AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one]
    rw [hdiag_inv, hM]
    all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
  have hdet : M.det = -(a₁ * a₂)⁻¹ := by
    rw [hM, Matrix.det_fin_three]
    simp
    try ring

  have hN : ∀ v : Fin 2 → ℝ,
      Matrix.of ![fun b => M 0 b + v 0 * M 2 b, fun b => M 1 b + v 1 * M 2 b] = !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0] := by
    intro v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, div_eq_mul_inv]
  rw [jacquetVector3_eq, hR, hdet]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only [jacquetIntegrand3, godementInner3, hR, hN]

#print axioms solution

end S_LanglandsTunnell_CubicInduction_jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq (solution)
