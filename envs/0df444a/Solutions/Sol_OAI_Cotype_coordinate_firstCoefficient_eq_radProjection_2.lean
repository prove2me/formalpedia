-- Prove2me | solution 2 for OAI.Cotype.coordinate_firstCoefficient_eq_radProjection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:09:51.473925+00:00
-- url     : https://prove2.me/submissions/d090f59f-22df-4f99-b59f-5b9eeee14b88

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CubeFirstChaos.lean:L54-L76
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.coordinate_firstCoefficient_eq_radProjection. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_projectionLinearCoefficient_eigenvector

-- ---- from OAI.Analysis.Cotype.Cube ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem character_symm (p ε : ι → Bool) : character p ε = character ε p := by
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> cases ε i <;> rfl

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.Damping ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem character_xor (P ε η : ι → Bool) :
    character P (xorCube ε η) = character P ε * character P η := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases P i <;> simp [xorCube]

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

theorem vectorWalsh_inversion {n : ℕ} (f : Cube n → X) (ε : Cube n) :
    (∑ p : Cube n, character p ε • vectorWalsh f p) = f ε := by
  classical
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ho η : (∑ p : Cube n, character p ε*character p η) =
      if ε=η then (Fintype.card (Cube n) : ℝ) else 0 := by
    simp_rw [character_symm _ ε, character_symm _ η]
    exact character_orthogonality ε η
  calc
    _ = ∑ η : Cube n, ((Fintype.card (Cube n) : ℝ)⁻¹ *
        ∑ p : Cube n, character p ε*character p η) • f η := by
      simp only [vectorWalsh, average, Finset.smul_sum, smul_smul,
        Finset.mul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro η _
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      ring
    _ = _ := by simp [ho]

theorem walshVector_inversion {n : ℕ} (f : PiLp 2 (fun _ : Cube n => X)) :
    (∑ p : Cube n, walshVector p (vectorWalsh (fun ε => f ε) p)) = f := by
  ext ε
  simpa [walshVector] using
    vectorWalsh_inversion (fun ε => f ε) ε

theorem coordinateExpectation_walshVector {n : ℕ} (i : Fin n) (p : Cube n) (x : X) :
    coordinateExpectation i (walshVector p x) =
      (if p i then (0 : ℝ) else 1) • walshVector p x := by
  ext ε
  have ht : character p (signCubeTwist (unitIndex i) ε) = sign (p i)*character p ε := by
    change character p (xorCube (unitIndex i) ε) = _
    rw [character_xor, character_symm p (unitIndex i), character_unitIndex]
  simp only [coordinateExpectation_apply, walshVector, PiLp.smul_apply, ht, smul_smul]
  cases hpi : p i <;> simp only [sign_false, sign_true, Bool.false_eq_true, ite_false, ite_true]
  all_goals module

theorem coordinate_firstCoefficient_eq_radProjection {n : ℕ} (f : Cube n → X) :
    projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) (toLp 2 f) =
      toLp 2 (radProjection X f) := by
  classical
  calc
    _ = projectionLinearCoefficient (coordinateExpectation (X := X) (n := n))
        (∑ p : Cube n, walshVector p (vectorWalsh f p)) := by
      rw [walshVector_inversion (toLp 2 f)]
    _ = ∑ p : Cube n, ∑ i : Fin n,
        if p = unitIndex i then walshVector p (vectorWalsh f p) else 0 := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact projectionLinearCoefficient_eigenvector
        (X := PiLp 2 (fun _ : Cube n => X)) (n := n)
        (fun i : Fin n => coordinateExpectation (X := X) i) p (walshVector p (vectorWalsh f p))
        (fun i => coordinateExpectation_walshVector i p (vectorWalsh f p))
    _ = ∑ i : Fin n, walshVector (unitIndex i) (vectorWalsh f (unitIndex i)) := by
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      ext ε
      simp [walshVector, radProjection, rademacherSum, vectorWalsh, moment]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.coordinate_firstCoefficient_eq_radProjection := @_root_.OAI.Cotype.coordinate_firstCoefficient_eq_radProjection
