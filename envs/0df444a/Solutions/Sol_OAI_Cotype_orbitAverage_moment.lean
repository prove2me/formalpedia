-- Prove2me | solution 1 for OAI.Cotype.orbitAverage_moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:12:24.998123+00:00
-- url     : https://prove2.me/submissions/0b41985f-ae29-4036-b6c6-13ba99d102d4

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

open OAI OAI.Cotype
open scoped BigOperators
variable {Γ I X : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]


theorem solution {m : ℕ} (ρ : Γ →* (X ≃ₗᵢ[ℝ] X))
    (x : I → Fin m → X) (hx : ∀ h a i, x (h • a) i = ρ h (x a i))
    (c : ℝ) (P : I → Cube m → X)
    (hP : ∀ a i, moment X (P a) i = c • x a i) (a : I) (i : Fin m) :
    moment X (fun ε => orbitAverage ρ (fun b => P b ε) a) i = c • x a i := by
  have hinv : ∀ g : Γ, ∀ y : X, ρ g (ρ g⁻¹ y) = y := by
    intro g y
    rw [map_inv]
    exact LinearIsometryEquiv.apply_symm_apply (ρ g) y
  have h1 : ∀ g : Γ, average (fun ε : Cube m => sign (ε i) • ρ g (P (g⁻¹ • a) ε)) = c • x a i := by
    intro g
    have : average (fun ε : Cube m => sign (ε i) • ρ g (P (g⁻¹ • a) ε))
        = ρ g (moment X (P (g⁻¹ • a)) i) := by
      simp only [moment, average, map_smul, map_sum]
    rw [this, hP, hx, map_smul, hinv]
  have h2 : moment X (fun ε => orbitAverage ρ (fun b => P b ε) a) i
      = average (fun g : Γ => average (fun ε : Cube m => sign (ε i) • ρ g (P (g⁻¹ • a) ε))) := by
    simp only [moment, orbitAverage, average, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    congr 1; ring
  have hc : (Fintype.card Γ : ℝ)⁻¹ * (Fintype.card Γ : ℝ) = 1 := by
    have : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [h2, show (fun g : Γ => average (fun ε : Cube m => sign (ε i) • ρ g (P (g⁻¹ • a) ε)))
      = fun _ => c • x a i from funext h1]
  simp only [average, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [← mul_assoc, hc, one_mul]

