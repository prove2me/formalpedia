-- Prove2me | solution 2 for OAI.Cotype.finiteProbabilityVector_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:20:52.695744+00:00
-- url     : https://prove2.me/submissions/78885961-0f86-4638-b057-b3850d8686ac

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/EquivariantPairing.lean:L22-L37
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.finiteProbabilityVector_norm. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing

-- ---- from OAI.Analysis.Cotype.EquivariantPairing ----
namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem finiteProbabilityVector_norm (f : Ω → X) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖finiteProbabilityVector f‖ ≤ 1 := by
  have hc : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos (α := Ω)
  have hb : ‖(toLp 2 f : PiLp 2 (fun _ : Ω => X))‖ ≤ Real.sqrt (Fintype.card Ω) := by
    rw [PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ _ : Ω, (1:ℝ) := Finset.sum_le_sum (fun a _ => by
        simpa using (sq_le_sq₀ (norm_nonneg (f a)) zero_le_one).mpr (hf a))
      _ = _ := by simp
  calc
    _ = Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) * ‖(toLp 2 f : PiLp 2 (fun _ : Ω => X))‖ := by
      rw [finiteProbabilityVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) * Real.sqrt (Fintype.card Ω) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = 1 := by rw [← Real.sqrt_mul (by positivity), inv_mul_cancel₀ hc.ne', Real.sqrt_one]

variable {n : ℕ}
end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.finiteProbabilityVector_norm := @_root_.OAI.Cotype.finiteProbabilityVector_norm
