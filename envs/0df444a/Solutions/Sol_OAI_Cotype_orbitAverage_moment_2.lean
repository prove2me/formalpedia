-- Prove2me | solution 2 for OAI.Cotype.orbitAverage_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:18:55.658802+00:00
-- url     : https://prove2.me/submissions/1f5b9863-33c7-46c5-b704-457f0e4f8671

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/EquivariantLifts.lean:L41-L61
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.orbitAverage_moment. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.EquivariantLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Γ I X : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [Fintype Γ] in
theorem isometryAction_mul (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (g h : Γ) (z : X) :
    ρ (g*h) z = ρ g (ρ h z) := by rw [map_mul]; rfl

omit [Fintype Γ] in
theorem isometryAction_one (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (z : X) :
    ρ 1 z = z := by rw [map_one]; rfl

theorem orbitAverage_moment {m : ℕ} (ρ : Γ →* (X ≃ₗᵢ[ℝ] X))
    (x : I → Fin m → X) (hx : ∀ h a i, x (h • a) i = ρ h (x a i))
    (c : ℝ) (P : I → Cube m → X)
    (hP : ∀ a i, moment X (P a) i = c • x a i) (a : I) (i : Fin m) :
    moment X (fun ε => orbitAverage ρ (fun b => P b ε) a) i = c • x a i := by
  have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (g : Γ) : ρ g (moment X (P (g⁻¹ • a)) i) = c • x a i := by
    rw [hP, map_smul, hx]
    rw [← isometryAction_mul, mul_inv_cancel, isometryAction_one]
  calc
    _ = average (fun g : Γ => ρ g (moment X (P (g⁻¹ • a)) i)) := by
      unfold moment orbitAverage
      simp only [average, map_smul, map_sum, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro ε _
      congr 1
      ring
    _ = c • x a i := by simp [he, average, ← Nat.cast_smul_eq_nsmul ℝ, hc, smul_smul]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.orbitAverage_moment := @_root_.OAI.Cotype.orbitAverage_moment
