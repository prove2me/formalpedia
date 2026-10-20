-- Prove2me | solution 2 for OAI.Cotype.matrixTwist_row_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:47:58.293521+00:00
-- url     : https://prove2.me/submissions/d6167295-08c9-4b22-9819-6d9395c7226b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PatternProjections.lean:L50-L91
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.matrixTwist_row_projection. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem average_negate {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : (ι → Bool) → E) : average (fun ε => f (negateCube ε)) = average f := by
  unfold average
  congr 1
  exact Fintype.sum_equiv negateEquiv _ _ (fun _ => rfl)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

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

theorem average_translate {n : ℕ} (a : Cube n) (f : Cube n → X) :
    average (fun u => f (xorCube a u)) = average f := average_equiv (cubeTranslate a) f

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

theorem average_add_real (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub_real (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_div_real (f : α → ℝ) (c : ℝ) :
    average (fun x => f x / c) = average f / c := by
  simp only [div_eq_mul_inv, average_mul_right]

theorem average_const_real [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  simp [average]

theorem average_coordinate {m : ℕ} (i : Fin m) (F : Bool → ℝ) :
    average (fun ε : Cube m => F (ε i)) = (F false + F true) / 2 := by
  have hn := average_negate (fun ε : Cube m => F (ε i))
  have hs : average (fun ε : Cube m => F (ε i) + F (!(ε i))) = F false + F true := by
    calc
      _ = average (fun _ : Cube m => F false + F true) := by
        congr 1; funext ε; cases ε i <;> simp [add_comm]
      _ = _ := average_const_real _
  rw [average_add_real] at hs
  change average (fun ε : Cube m => F (!(ε i))) = _ at hn
  rw [hn] at hs
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem xorCube_negate_right (a b : ι → Bool) :
    xorCube a (negateCube b) = negateCube (xorCube a b) := by
  funext i; simp [xorCube, negateCube]

theorem oddPart_vectorTwist {m : ℕ} (φ : Cube m → Cube m → ℝ) (s : Cube m) :
    oddPart (vectorTwist φ) s = average (fun ε => oddPart (fun s => φ s ε) (xorCube ε s)) := by
  simp only [oddPart, vectorTwist, xorCube_negate_right, average_div_real, average_sub_real]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternProjections ----
namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

theorem row_twist_change (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (S : SignMatrix m) (ε δ : Cube m) (i : Fin m) :
    average (fun σ : Cube m => sign (σ i) * Φ (dampedSample ε δ (xorCube (rowCube σ) S)) ε δ) =
    average (fun ξ : Cube m => (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ δ S) ε δ) := by
  rw [← average_translate ε (fun ξ : Cube m =>
    (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ δ S) ε δ)]
  congr 1
  funext σ
  have he : dampedSample (xorCube ε σ) δ S = dampedSample ε δ (xorCube (rowCube σ) S) := by
    funext ij
    simp [dampedSample, xorCube, rowCube, columnCube, Bool.xor_left_comm]
  rw [he]
  change _ = (sign (ε i) * sign (Bool.xor (ε i) (σ i))) * _
  rw [sign_xor, ← mul_assoc (sign (ε i)), sign_sq, one_mul]

theorem sign_coordinate_odd (ψ : Cube m → ℝ) (i : Fin m) (s : Cube m) :
    average (fun ξ : Cube m => sign (ξ i) * ψ (fun j => Bool.xor (ξ i) (s j))) = oddPart ψ s := by
  rw [average_coordinate i (fun b => sign b * ψ (fun j => Bool.xor b (s j)))]
  simp [oddPart, sub_eq_add_neg]
  rfl

theorem matrixTwist_row_projection (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (ψ : Cube m → Cube m → ℝ) (a : ℝ)
    (hm : ∀ S δ i, moment ℝ (fun ε => Φ S ε δ) i = a * ψ (fun j => S (i,j)) δ)
    (i : Fin m) (S : SignMatrix m) :
    rowProjection (matrixTwist Φ) i S = a * oddPart (vectorTwist ψ) (fun j => S (i,j)) := by
  calc
    _ = average (fun ε => average (fun δ => average (fun σ : Cube m =>
        sign (σ i) * Φ (dampedSample ε δ (xorCube (rowCube σ) S)) ε δ))) := by
      unfold rowProjection matrixTwist
      simp only [← average_mul_left]
      rw [average_comm]
      congr 1; funext ε; rw [average_comm]
    _ = average (fun ε => average (fun δ => average (fun ξ : Cube m =>
        (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ δ S) ε δ))) := by
      simp_rw [row_twist_change]
    _ = average (fun ξ : Cube m => average (fun δ : Cube m =>
        sign (ξ i) * moment ℝ (fun ε => Φ (dampedSample ξ δ S) ε δ) i)) := by
      rw [average_comm]
      simp_rw [average_comm (fun ε ξ : Cube m =>
        (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ _ S) ε _)]
      rw [average_comm]
      congr 1; funext ξ
      congr 1; funext δ
      simp only [moment, smul_eq_mul, ← average_mul_left]
      congr 1; funext ε; ring
    _ = average (fun ξ : Cube m => average (fun δ : Cube m =>
        sign (ξ i) * (a * ψ (fun j => dampedSample ξ δ S (i,j)) δ))) := by simp_rw [hm]
    _ = a * average (fun δ : Cube m => average (fun ξ : Cube m =>
        sign (ξ i) * ψ (fun j => Bool.xor (ξ i) ((xorCube δ (fun j => S (i,j))) j)) δ)) := by
      rw [average_comm]
      simp only [← average_mul_left]
      congr 1; funext δ
      congr 1; funext ξ
      dsimp [dampedSample, rowCube, columnCube, xorCube]
      ring
    _ = _ := by
      have he (δ : Cube m) : average (fun ξ : Cube m => sign (ξ i) *
          ψ (fun j => Bool.xor (ξ i) ((xorCube δ (fun j => S (i,j))) j)) δ) =
          oddPart (fun s => ψ s δ) (xorCube δ (fun j => S (i,j))) :=
        sign_coordinate_odd (fun s => ψ s δ) i _
      simp_rw [he]
      rw [oddPart_vectorTwist]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.matrixTwist_row_projection := @_root_.OAI.Cotype.matrixTwist_row_projection
