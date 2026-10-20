-- Prove2me | solution 2 for OAI.Cotype.exists_type_extrapolation_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:47:16.476504+00:00
-- url     : https://prove2.me/submissions/3cb2d65c-52d3-44e7-abb1-2dfc83a6a0a3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TypeExtrapolationParameters.lean:L28-L65
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_type_extrapolation_parameters. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.TypeExtrapolationParameters ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_type_extrapolation_parameters {n : ℕ} (hn : 1 < n) {A : ℝ}
    (hA : 0 ≤ A) (hAn : A < n) :
    ∃ p r : ℝ, 1 < p ∧ p ≤ 2 ∧ 1 < r ∧ r^p = n ∧
      0 ≤ Real.sqrt (A*n)*r⁻¹ ∧ Real.sqrt (A*n)*r⁻¹ < 1 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsA : Real.sqrt (A*n) < n := by
    apply (Real.sqrt_lt' hn0).mpr
    nlinarith
  have hsn : Real.sqrt (n : ℝ) < n := by
    apply (Real.sqrt_lt' hn0).mpr
    nlinarith
  let t := max (Real.sqrt (A*n)) (Real.sqrt (n : ℝ))
  have ht : t < n := max_lt hsA hsn
  let r := (t+n)/2
  have htr : t < r := by dsimp [r]; linarith
  have hrn : r < n := by dsimp [r]; linarith
  have hsqr : Real.sqrt (n : ℝ) < r := (le_max_right _ _).trans_lt htr
  have hs1 : 1 < Real.sqrt (n : ℝ) := by
    exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hn1)
  have hr : 1 < r := hs1.trans hsqr
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hlog : Real.log r < Real.log n := Real.log_lt_log hr0 hrn
  have hnsq : (n : ℝ) < r^2 := by nlinarith [Real.sq_sqrt hn0.le,Real.sqrt_nonneg (n : ℝ)]
  have hlog2 : Real.log n < 2*Real.log r := by
    have hh := Real.log_lt_log hn0 hnsq
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  let p := Real.log n / Real.log r
  have hp : 1 < p := (one_lt_div hlr).mpr hlog
  have hp2 : p ≤ 2 := (div_le_iff₀ hlr).mpr hlog2.le
  have hrp : r^p = (n : ℝ) := by
    rw [Real.rpow_def_of_pos hr0]
    have he : Real.log r * p = Real.log n := by dsimp [p]; field_simp
    rw [he,Real.exp_log hn0]
  refine ⟨p,r,hp,hp2,hr,hrp,mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hr0.le),?_⟩
  have hAr : Real.sqrt (A*n) < r := (le_max_left _ _).trans_lt htr
  exact (mul_inv_lt_iff₀ hr0).mpr (by simpa using hAr)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_type_extrapolation_parameters := @_root_.OAI.Cotype.exists_type_extrapolation_parameters
