-- Prove2me | solution 2 for OAI.Cotype.geometric_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:55:21.864758+00:00
-- url     : https://prove2.me/submissions/5f4c146b-e08f-4400-b456-49cfed731c9f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GeometricTypeLevels.lean:L77-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.geometric_block_bound. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_QuadraticTypeBound_support

-- ---- from OAI.Analysis.Cotype.GeometricTypeLevels ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem geometric_block_bound {N n k : ℕ} {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r)
    (h : QuadraticTypeBound X (n^(k+1)) (A^(k+1)))
    (s : Finset (Fin N)) (hs : s.card ≤ n^(k+1))
    (x : Fin N → X) (hx0 : ∀ i, i ∉ s → x i = 0)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ (r⁻¹)^k) :
    cubeL2 X (rademacherSum X x) ≤
      Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by
  classical
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hAn : 0 ≤ A*n := mul_nonneg hA hn
  have hmass : (∑ i, ‖x i‖^2) ≤ (n : ℝ)^(k+1)*((r⁻¹)^k)^2 := by
    calc
      _ = ∑ i ∈ s, ‖x i‖^2 := (Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => by rw [hx0 i hi,norm_zero]; norm_num)).symm
      _ ≤ ∑ _i ∈ s, ((r⁻¹)^k)^2 := Finset.sum_le_sum (fun i hi =>
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hx i hi))
      _ = (s.card : ℝ)*((r⁻¹)^k)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
  have hb := (h.support s hs x hx0).trans (mul_le_mul_of_nonneg_left hmass (pow_nonneg hA _))
  let C := Real.sqrt (A*n)
  have hC : C^2 = A*n := Real.sq_sqrt hAn
  have hCk : (C^k)^2 = (A*n)^k := by rw [← pow_mul,mul_comm k 2,pow_mul,hC]
  have he : (C*(C*r⁻¹)^k)^2 = A^(k+1)*(n : ℝ)^(k+1)*((r⁻¹)^k)^2 := by
    rw [mul_pow,mul_pow,mul_pow,hC,hCk]
    simp only [mul_pow,pow_succ]
    ring
  apply (sq_le_sq₀ (cubeL2_nonneg _) (by positivity)).mp
  rw [he]
  simpa only [mul_assoc] using hb

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.geometric_block_bound := @_root_.OAI.Cotype.geometric_block_bound
