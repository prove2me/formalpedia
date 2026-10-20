-- Prove2me | solution 1 for OAI.Cotype.geometric_level_card_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:06:52.019912+00:00
-- url     : https://prove2.me/submissions/e0a8ba62-5992-4f13-af8e-34e5b770ba12

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]


omit [NormedSpace ℝ X] in
theorem solution {N n k : ℕ} (hn : 0 < n) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hrp : r^p = n)
    (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1)
    (s : Finset (Fin N)) (hs : ∀ i ∈ s, (r⁻¹)^(k+1) ≤ ‖x i‖) :
    s.card ≤ n^(k+1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : ∀ i ∈ s, ((n : ℝ) ^ (k + 1))⁻¹ ≤ ‖x i‖ ^ p := by
    intro i hi
    have h1 : ((r⁻¹) ^ (k + 1)) ^ p ≤ ‖x i‖ ^ p :=
      Real.rpow_le_rpow (by positivity) (hs i hi) hp.le
    calc ((n : ℝ) ^ (k + 1))⁻¹ = ((r⁻¹) ^ (k + 1)) ^ p := by
          rw [← hrp, inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast r,
            ← Real.rpow_natCast (r ^ p), ← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le, mul_comm]
      _ ≤ _ := h1
  have hsum : (s.card : ℝ) * ((n : ℝ) ^ (k + 1))⁻¹ ≤ 1 := by
    calc (s.card : ℝ) * ((n : ℝ) ^ (k + 1))⁻¹ = ∑ _i ∈ s, ((n : ℝ) ^ (k + 1))⁻¹ := by simp
      _ ≤ ∑ i ∈ s, ‖x i‖ ^ p := Finset.sum_le_sum hb
      _ ≤ ∑ i, ‖x i‖ ^ p := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)
      _ ≤ 1 := hx
  have hpos : (0 : ℝ) < (n : ℝ) ^ (k + 1) := by positivity
  rw [← div_eq_mul_inv, div_le_one hpos] at hsum
  exact_mod_cast hsum

