-- Prove2me | solution 1 for OAI.Cotype.exists_geometric_levels
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:05:57.008329+00:00
-- url     : https://prove2.me/submissions/3a3afaf8-4897-4677-85fa-1b1cdbccaddc

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
theorem solution {N : ℕ} {r : ℝ} (hr : 1 < r)
    (x : Fin N → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ l : Fin N → ℕ, ∀ i, ‖x i‖ ≤ (r⁻¹)^(l i) ∧
      (x i ≠ 0 → (r⁻¹)^(l i+1) < ‖x i‖) := by
  have hr0 : 0 < r⁻¹ := inv_pos.mpr (by linarith)
  have hr1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  classical
  have hex : ∀ i, x i ≠ 0 → ∃ l : ℕ, (r⁻¹) ^ (l + 1) < ‖x i‖ := by
    intro i hi
    obtain ⟨l, hl⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hi) hr1
    exact ⟨l, lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ l)) hl⟩
  refine ⟨fun i => if hi : x i = 0 then 0 else Nat.find (hex i hi), fun i => ?_⟩
  by_cases hi : x i = 0
  · simp only [hi, dite_true, pow_zero, norm_zero, zero_le_one, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, and_self]
  · simp only [hi, dite_false]
    refine ⟨?_, fun _ => Nat.find_spec (hex i hi)⟩
    rcases h : Nat.find (hex i hi) with _ | k
    · simpa using hx i
    · have := Nat.find_min (hex i hi) (show k < Nat.find (hex i hi) by omega)
      exact le_of_not_gt this

