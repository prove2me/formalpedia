-- Prove2me | solution 2 for OAI.Cotype.hasType_of_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:48:52.844197+00:00
-- url     : https://prove2.me/submissions/b52e5a3c-166c-431a-807d-dd46895af977

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TypeExtrapolationParameters.lean:L67-L108
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.hasType_of_normalized_bound. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cubeL2_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    cubeL2 X (fun ε => a • f ε) = |a| * cubeL2 X f := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => a • f ε) : PiLp 2 (fun _ : Cube n => X)) =
      a • toLp 2 f := rfl
  rw [he, norm_smul, Real.norm_eq_abs]
  ring

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeExtrapolationParameters ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasType_of_normalized_bound {p D : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hD : 0 ≤ D)
    (h : ∀ (n : ℕ) (x : Fin n → X), (∑ i, ‖x i‖^p) ≤ 1 →
      cubeL2 X (rademacherSum X x) ≤ D) : HasType X p := by
  classical
  have hp0 : 0 < p := by linarith
  refine ⟨hp,hp2,D,hD,fun n x => ?_⟩
  let S : ℝ := ∑ i, ‖x i‖^p
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hz : S = 0
  · have hx : ∀ i, x i = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Real.rpow_nonneg (norm_nonneg (x j)) p)
        (Finset.mem_univ i)
      change ‖x i‖^p ≤ S at hi
      rw [hz] at hi
      by_contra hxi
      have hh := Real.rpow_pos_of_pos (norm_pos_iff.mpr hxi) p
      linarith
    simp [hx,rademacherSum,cubeL2,average,Real.zero_rpow (ne_of_gt hp0) ]
    positivity
  have hS0 : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  let r := S^(1/p)
  have hr : 0 < r := Real.rpow_pos_of_pos hS0 _
  have hrp : r^p = S := by
    dsimp [r]
    rw [← Real.rpow_mul hS,div_mul_cancel₀ 1 (ne_of_gt hp0),Real.rpow_one]
  let y : Fin n → X := fun i => r⁻¹ • x i
  have hy : (∑ i, ‖y i‖^p) = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hr.le),
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg _),← Finset.mul_sum]
    change (r⁻¹)^p*S = 1
    rw [Real.inv_rpow hr.le,hrp,inv_mul_cancel₀ hz]
  have he : rademacherSum X y = fun ε => r⁻¹ • rademacherSum X x ε := by
    funext ε
    simp only [y,rademacherSum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  have hh := h n y hy.le
  rw [he,cubeL2_smul,abs_of_nonneg (inv_nonneg.mpr hr.le)] at hh
  have hh' := (inv_mul_le_iff₀ hr).mp hh
  simpa only [r,S,mul_comm] using hh'

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.hasType_of_normalized_bound := @_root_.OAI.Cotype.hasType_of_normalized_bound
