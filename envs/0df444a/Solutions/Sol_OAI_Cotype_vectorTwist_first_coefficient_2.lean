-- Prove2me | solution 2 for OAI.Cotype.vectorTwist_first_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:44:02.617822+00:00
-- url     : https://prove2.me/submissions/c7335f3a-0d7b-4b49-9695-3b9e3cc628bc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PatternNormalization.lean:L87-L106
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.vectorTwist_first_coefficient. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Theorems.Thm_OAI_Cotype_fourier_inversion
import Theorems.Thm_OAI_Cotype_fourier_oddPart

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem oddPart_preserves_odd_coefficient (f : (ι → Bool) → ℝ)
    {p : ι → Bool} (hp : paritySign p = -1) :
    fourier (oddPart f) p = fourier f p := by
  rw [fourier_oddPart, hp]
  ring

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

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

-- ---- from OAI.Analysis.Cotype.WalshExactPairing ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem average_const_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → X) :
    average (fun a => c • f a) = c • average f := by
  simp only [average, Finset.smul_sum, smul_smul]
  simp only [mul_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionCoefficients ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem fourier_const_mul (f : (ι → Bool) → ℝ) (a : ℝ) (p : ι → Bool) :
    fourier (fun S => a * f S) p = a * fourier f p := by
  simp only [fourier, average, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem fourier_sum {α : Type*} [Fintype α] (f : α → (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun S => ∑ i, f i S) p = ∑ i, fourier (f i) p := by
  simp only [fourier, Finset.sum_mul, average_sum]

theorem fourier_character (p q : ι → Bool) :
    fourier (character p) q = if p = q then 1 else 0 := average_character_mul p q

theorem fourier_translate (f : (ι → Bool) → ℝ) (δ p : ι → Bool) :
    fourier (fun S => f (xorCube δ S)) p = fourier f p * character p δ := by
  have he : (fun S => f (xorCube δ S)) =
      fun S => ∑ q, (fourier f q * character q δ) * character q S := by
    funext S
    rw [← fourier_inversion f (xorCube δ S)]
    simp [character_xor, mul_assoc]
  rw [he, fourier_sum]
  simp_rw [fourier_const_mul, fourier_character]
  simp

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternNormalization ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {α : Type*} [Fintype α]

theorem average_mul_left (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := average_const_smul c f

theorem average_mul_right (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := average_smul_const f c

theorem average_const_real [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  simp [average]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fourier_average_family (F : α → (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun s => average (fun a => F a s)) p = average (fun a => fourier (F a) p) := by
  simp only [fourier, ← average_mul_right]
  rw [average_comm]

theorem vectorTwist_first_coefficient {m : ℕ} (φ : Cube m → Cube m → ℝ)
    (c : ℝ) (hm : ∀ s i, moment ℝ (φ s) i = c * sign (s i)) (i : Fin m) :
    fourier (oddPart (vectorTwist φ)) (unitIndex i) = c := by
  rw [oddPart_preserves_odd_coefficient _ (by simp [paritySign, unitIndex])]
  unfold vectorTwist
  rw [fourier_average_family]
  have ht (ε : Cube m) : fourier (fun s => φ (xorCube ε s) ε) (unitIndex i) =
      fourier (fun s => φ s ε) (unitIndex i) * sign (ε i) := by
    exact (fourier_translate (fun s => φ s ε) ε (unitIndex i)).trans (by rw [character_unitIndex])
  simp_rw [ht]
  simp only [fourier, character_unitIndex, ← average_mul_right]
  rw [average_comm]
  have he (s : Cube m) : average (fun ε => φ s ε * sign (s i) * sign (ε i)) = c := by
    calc
      _ = sign (s i) * moment ℝ (φ s) i := by
        simp only [moment, smul_eq_mul, ← average_mul_left]
        congr 1; funext ε; ring
      _ = c := by rw [hm, mul_left_comm, sign_sq, mul_one]
  simp_rw [he]
  exact average_const_real c

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.vectorTwist_first_coefficient := @_root_.OAI.Cotype.vectorTwist_first_coefficient
