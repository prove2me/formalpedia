-- Prove2me | solution 1 for OAI.Cotype.GrowthPairingData.exists_fixed_lift_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:15:10.10298+00:00
-- url     : https://prove2.me/submissions/e57b5adb-7e1a-47b2-88ae-a793dbdac32c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GrowthCoefficient.lean:L54-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.GrowthPairingData.exists_fixed_lift_coefficient. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation
import Definitions.Def_OAI_Analysis_Cotype_BivariateSplit
import Definitions.Def_OAI_Analysis_Cotype_ProjectionDerivatives
import Definitions.Def_OAI_Analysis_Cotype_MixedDerivative
import Definitions.Def_OAI_Analysis_Cotype_CoefficientCompactness
import Definitions.Def_OAI_Analysis_Cotype_GrowthScalarData
import Theorems.Thm_OAI_Cotype_fourier_inversion
import Theorems.Thm_OAI_Cotype_fourier_oddPart

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem oddPart_isOdd (f : (ι → Bool) → ℝ) : IsOdd (oddPart f) := by
  intro ε
  simp only [oddPart, negateCube_negateCube]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem oddPart_eq_self {f : (ι → Bool) → ℝ} (hf : IsOdd f) : oddPart f = f := by
  funext ε
  dsimp [oddPart]
  rw [hf]
  ring

theorem odd_even_coefficient_zero {f : (ι → Bool) → ℝ} (hf : IsOdd f)
    {p : ι → Bool} (hp : paritySign p = 1) : fourier f p = 0 := by
  have h := fourier_oddPart f p
  rw [oddPart_eq_self hf, hp] at h
  simpa using h

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

theorem average_mul_right (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := average_smul_const f c

theorem average_const_real [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  simp [average]

theorem abs_average_le_const [Nonempty α] (f : α → ℝ) {M : ℝ}
    (hf : ∀ a, |f a| ≤ M) : |average f| ≤ M := by
  calc
    _ ≤ average (fun a => |f a|) := by simpa only [Real.norm_eq_abs] using norm_average_le f
    _ ≤ average (fun _ : α => M) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hf a)) (by positivity)
    _ = M := average_const_real M

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fourier_average_family (F : α → (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun s => average (fun a => F a s)) p = average (fun a => fourier (F a) p) := by
  simp only [fourier, ← average_mul_right]
  rw [average_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GrowthCoefficient ----
namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

theorem abs_character_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (P s : ι → Bool) :
    |character P s| = 1 := by
  rcases mul_self_eq_one_iff.mp (character_sq P s) with h | h <;> simp [h]

theorem fourier_matrixTwist (Φ : SignMatrix m → Cube m → Cube m → ℝ) (P : SignMatrix m) :
    fourier (matrixTwist Φ) P = average (fun ε => average (fun δ =>
      fourier (fun S => Φ S ε δ) P * character P (xorCube (rowCube ε) (columnCube δ)))) := by
  unfold matrixTwist
  rw [fourier_average_family]
  have ht (ε δ : Cube m) : fourier (fun S => Φ (dampedSample ε δ S) ε δ) P =
      fourier (fun S => Φ S ε δ) P * character P (xorCube (rowCube ε) (columnCube δ)) := by
    have he (S : SignMatrix m) : dampedSample ε δ S = xorCube (xorCube (rowCube ε) (columnCube δ)) S := by
      funext ij; simp [dampedSample, xorCube]
    simp_rw [he]
    exact fourier_translate (fun S => Φ S ε δ) _ P
  simp_rw [fourier_average_family, ht]

theorem paritySign_one_or_neg_one (P : SignMatrix m) : paritySign P = 1 ∨ paritySign P = -1 := by
  have h := character_sq P (fun _ => true)
  change paritySign P * paritySign P = 1 at h
  exact mul_self_eq_one_iff.mp h

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n k : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

theorem normalized_coefficient_identity (hn : m+m ≤ n) (P : SignMatrix m)
    (hp : fourier (d.normalizedMatrix hn) P ≠ 0) :
    d.gamma * fourier (d.normalizedMatrix hn) P = average (fun ε => average (fun δ =>
      fourier (fun S => d.patternPairing hn S ε δ) P *
        character P (xorCube (rowCube ε) (columnCube δ)))) := by
  have ho : IsOdd (d.normalizedMatrix hn) := by
    intro S; unfold normalizedMatrix; rw [oddPart_isOdd]; ring
  have hpar : paritySign P = -1 := by
    rcases paritySign_one_or_neg_one P with h | h
    · exact False.elim (hp (odd_even_coefficient_zero ho h))
    · exact h
  unfold normalizedMatrix
  rw [fourier_const_mul, oddPart_preserves_odd_coefficient _ hpar]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt d.gamma_pos), one_mul]
  exact fourier_matrixTwist _ P

theorem exists_fixed_lift_coefficient (hn : m+m ≤ n) (P : SignMatrix m)
    {c : ℝ} (hc : 0 < c) (hp : c ≤ |fourier (d.normalizedMatrix hn) P|) :
    ∃ ε δ : Cube m, c * d.gamma ≤ |fourier (fun S => d.patternPairing hn S ε δ) P| := by
  have hp0 : fourier (d.normalizedMatrix hn) P ≠ 0 := abs_pos.mp (hc.trans_le hp)
  obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Cube m × Cube m))
    (fun z => |fourier (fun S => d.patternPairing hn S z.1 z.2) P|) Finset.univ_nonempty
  refine ⟨z.1,z.2,?_⟩
  have hb : |d.gamma * fourier (d.normalizedMatrix hn) P| ≤
      |fourier (fun S => d.patternPairing hn S z.1 z.2) P| := by
    rw [d.normalized_coefficient_identity hn P hp0]
    apply abs_average_le_const
    intro ε
    apply abs_average_le_const
    intro δ
    rw [abs_mul, abs_character_finite, mul_one]
    exact hmax (ε,δ) (Finset.mem_univ _)
  rw [abs_mul, abs_of_pos d.gamma_pos] at hb
  exact (mul_le_mul_of_nonneg_right hp (le_of_lt d.gamma_pos)).trans (by simpa [mul_comm] using hb)

variable (d : GrowthPairingData T (k+m+m) m Dg Df)

end GrowthPairingData

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype OAI.Cotype.GrowthPairingData


theorem solution : type_of% @_root_.OAI.Cotype.GrowthPairingData.exists_fixed_lift_coefficient := @_root_.OAI.Cotype.GrowthPairingData.exists_fixed_lift_coefficient
