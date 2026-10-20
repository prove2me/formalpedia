-- Prove2me | solution 2 for OAI.Cotype.kConvex_iff_coordinate_firstCoefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:11:49.055331+00:00
-- url     : https://prove2.me/submissions/6d4eda40-000e-4ba7-9fb5-12ac5bb0b912

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/KConvexCoordinateCriterion.lean:L11-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.kConvex_iff_coordinate_firstCoefficient_bound. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_coordinate_firstCoefficient_eq_radProjection

-- ---- from OAI.Analysis.Cotype.FiniteL2Dual ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω]

theorem probabilityL2Vector_norm {n : ℕ} (f : Cube n → X) :
    ‖probabilityL2Vector f‖ = cubeL2 X f := by
  rw [probabilityL2Vector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    cubeL2_eq_piLp]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CubeFirstChaos ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem coordinate_firstCoefficient_probabilityL2_norm {n : ℕ} (f : Cube n → X) :
    ‖projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) (probabilityL2Vector f)‖ =
      cubeL2 X (radProjection X f) := by
  rw [probabilityL2Vector, map_smul, coordinate_firstCoefficient_eq_radProjection]
  exact probabilityL2Vector_norm (radProjection X f)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.KConvexCoordinateCriterion ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem kConvex_iff_coordinate_firstCoefficient_bound :
    KConvex X ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : PiLp 2 (fun _ : Cube n => X)),
      ‖projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) f‖ ≤ K*‖f‖ := by
  constructor
  · rintro ⟨K,hK,h⟩
    refine ⟨K,hK,fun n f => ?_⟩
    have hb := h n (fun ε => f ε)
    rw [cubeL2_eq_piLp, cubeL2_eq_piLp] at hb
    have hc : 0 < Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) := by
      apply Real.sqrt_pos.mpr
      apply inv_pos.mpr
      exact_mod_cast Fintype.card_pos
    have he := coordinate_firstCoefficient_eq_radProjection (fun ε => f ε)
    have hf : (toLp 2 (fun ε => f ε) : PiLp 2 (fun _ : Cube n => X)) = f := by ext ε; rfl
    rw [hf] at he
    rw [he]
    apply (mul_le_mul_iff_left₀ hc).mp
    simpa only [hf, mul_comm, mul_left_comm, mul_assoc] using hb
  · rintro ⟨K,hK,h⟩
    refine ⟨K,hK,fun n f => ?_⟩
    have hb := h n (probabilityL2Vector f)
    rwa [coordinate_firstCoefficient_probabilityL2_norm, probabilityL2Vector_norm] at hb

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.kConvex_iff_coordinate_firstCoefficient_bound := @_root_.OAI.Cotype.kConvex_iff_coordinate_firstCoefficient_bound
