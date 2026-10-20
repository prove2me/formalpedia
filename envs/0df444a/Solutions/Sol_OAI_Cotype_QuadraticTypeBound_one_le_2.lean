-- Prove2me | solution 2 for OAI.Cotype.QuadraticTypeBound.one_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:45:38.946697+00:00
-- url     : https://prove2.me/submissions/9524b290-6b45-48e0-98c7-3887bc436be5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TypeExtrapolationParameters.lean:L11-L26
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.QuadraticTypeBound.one_le. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.QuadraticTypeTensor ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_const_value {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average,smul_eq_mul]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeExtrapolationParameters ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem QuadraticTypeBound.one_le [Nontrivial X] {n : ℕ} (hn : 0 < n)
    {A : ℝ} (h : QuadraticTypeBound X n A) : 1 ≤ A := by
  classical
  obtain ⟨u,hu⟩ := exists_ne (0 : X)
  let v : X := ‖u‖⁻¹ • u
  have hv : ‖v‖ = 1 := by
    rw [show v = ‖u‖⁻¹ • u from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  let i : Fin n := ⟨0,hn⟩
  let x : Fin n → X := fun j => if j = i then v else 0
  have hs : (∑ j, ‖x j‖^2) = 1 := by simp [x,apply_ite,hv]
  have hr (ε : Cube n) : ‖rademacherSum X x ε‖^2 = 1 := by
    simp only [rademacherSum,x,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    cases ε i <;> simp [hv]
  have hh := h x
  simpa only [cubeL2_sq,hr,average_const_value,hs,mul_one] using hh

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.QuadraticTypeBound.one_le := @_root_.OAI.Cotype.QuadraticTypeBound.one_le
