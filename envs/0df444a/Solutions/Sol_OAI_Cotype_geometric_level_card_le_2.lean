-- Prove2me | solution 2 for OAI.Cotype.geometric_level_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:53:48.114329+00:00
-- url     : https://prove2.me/submissions/77dd807a-be90-4076-b9f6-f4c25ea80f6b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GeometricTypeLevels.lean:L55-L75
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.geometric_level_card_le. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.GeometricTypeLevels ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem real_pow_rpow_comm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (a^k)^p = (a^p)^k := by
  rw [← Real.rpow_natCast_mul ha,← Real.rpow_mul_natCast ha]
  congr 1
  ring

omit [NormedSpace ℝ X] in

theorem geometric_level_card_le {N n k : ℕ} (hn : 0 < n) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hrp : r^p = n)
    (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1)
    (s : Finset (Fin N)) (hs : ∀ i ∈ s, (r⁻¹)^(k+1) ≤ ‖x i‖) :
    s.card ≤ n^(k+1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : ((r⁻¹)^(k+1))^p = ((n : ℝ)^(k+1))⁻¹ := by
    rw [real_pow_rpow_comm _ (inv_nonneg.mpr hr.le),Real.inv_rpow hr.le,hrp,inv_pow]
  have hlo : (s.card : ℝ)*((n : ℝ)^(k+1))⁻¹ ≤ ∑ i ∈ s, ‖x i‖^p := by
    rw [← he]
    calc
      _ = ∑ _i ∈ s, ((r⁻¹)^(k+1))^p := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => Real.rpow_le_rpow (by positivity) (hs i hi) hp.le)
  have hhi : (∑ i ∈ s, ‖x i‖^p) ≤ 1 := by
    apply le_trans _ hx
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hh := (mul_inv_le_iff₀ (pow_pos hn0 (k+1))).mp (hlo.trans hhi)
  have hh' : (s.card : ℝ) ≤ (n : ℝ)^(k+1) := by simpa using hh
  exact_mod_cast hh'

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.geometric_level_card_le := @_root_.OAI.Cotype.geometric_level_card_le
