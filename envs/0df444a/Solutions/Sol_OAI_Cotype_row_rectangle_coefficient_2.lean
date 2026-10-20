-- Prove2me | solution 2 for OAI.Cotype.row_rectangle_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:41:58.734189+00:00
-- url     : https://prove2.me/submissions/fa731015-36a8-4cb6-8a23-67e02d3b6284

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionCoefficients.lean:L90-L110
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.row_rectangle_coefficient. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_fourier_inversion
import Theorems.Thm_OAI_Cotype_fourier_oddPart

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem paritySign_eq (p : ι → Bool) :
    paritySign p = (-1 : ℝ) ^ (Finset.univ.filter (fun i => p i = true)).card := by
  simp [paritySign, ← Finset.prod_filter]

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

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.BinaryRank ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem paritySign_rectangle (s : Finset ι) (t : Finset κ) :
    paritySign (rectangle s t) = (-1 : ℝ) ^ (s.card * t.card) := by
  rw [paritySign_eq]
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  rw [he, Finset.card_product]

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

theorem character_setIndex (s : Finset ι) (ε : ι → Bool) :
    character (setIndex s) ε = ∏ i ∈ s, sign (ε i) := by
  simp [character, setIndex]

theorem character_rectangle (s : Finset ι) (t : Finset κ) (S : (ι × κ) → Bool) :
    character (rectangle s t) S = ∏ i ∈ s, ∏ j ∈ t, sign (S (i,j)) := by
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  unfold character
  rw [← Finset.prod_filter, he, Finset.prod_product]

theorem character_rectangle_row (s : Finset ι) (t : Finset κ)
    (ht : Odd t.card) (σ : ι → Bool) :
    character (rectangle s t) (rowCube σ) = character (setIndex s) σ := by
  rw [character_rectangle, character_setIndex]
  apply Finset.prod_congr rfl
  intro i _
  simp only [rowCube, Finset.prod_const]
  cases σ i <;> simp [ht.neg_one_pow]

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

theorem fourier_average_translate {α : Type*} [Fintype α]
    (f : (ι → Bool) → ℝ) (D : α → ι → Bool) (w : α → ℝ) (p : ι → Bool) :
    fourier (fun S => average (fun x => w x * f (xorCube (D x) S))) p =
      fourier f p * average (fun x => w x * character p (D x)) := by
  simp only [average, smul_eq_mul, fourier_const_mul, fourier_sum]
  simp_rw [fourier_translate]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem rowIndex_injective (i : ι) : Function.Injective (rowIndex (κ := κ) i) := by
  intro p q h
  funext j
  simpa using congrFun h (i,j)

omit [DecidableEq κ] in
theorem character_rowIndex (i : ι) (p : κ → Bool) (S : (ι × κ) → Bool) :
    character (rowIndex i p) S = character p (fun j => S (i,j)) := by
  simp only [character, Fintype.prod_prod_type]
  have he (a : ι) : (∏ j, if rowIndex i p (a,j) then sign (S (a,j)) else 1) =
      if a = i then ∏ j, if p j then sign (S (i,j)) else 1 else 1 := by
    by_cases h : a = i <;> simp [h, rowIndex]
  simp_rw [he]
  simp

theorem fourier_rowLift (g : (κ → Bool) → ℝ) (i : ι) (p : κ → Bool) :
    fourier (fun S : (ι × κ) → Bool => g (fun j => S (i,j))) (rowIndex i p) =
      fourier g p := by
  have he : (fun S : (ι × κ) → Bool => g (fun j => S (i,j))) =
      fun S => ∑ q, fourier g q * character (rowIndex i q) S := by
    funext S
    simp only [character_rowIndex, fourier_inversion]
  rw [he, fourier_sum]
  simp_rw [fourier_const_mul, fourier_character, (rowIndex_injective i).eq_iff]
  simp

omit [Fintype ι] [Fintype κ] in
theorem rowIndex_setIndex (i : ι) (t : Finset κ) :
    rowIndex i (setIndex t) = rectangle {i} t := by
  funext ij
  by_cases h : ij.1 = i <;> simp [rowIndex, rectangle, setIndex, h]

theorem paritySign_setIndex (t : Finset ι) : paritySign (setIndex t) = (-1 : ℝ)^t.card := by
  simp [paritySign_eq, setIndex]

theorem row_rectangle_coefficient {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {g : Cube n → ℝ} {a : ℝ} (hΨ : IsOdd Ψ) (hg : IsOdd g)
    (hp : ∀ (i : Fin m) S, average (fun σ : Cube m =>
      sign (σ i) * Ψ (xorCube (rowCube σ) S)) = a * g (fun j => S (i,j)))
    (i : Fin m) (t : Finset (Fin n)) :
    fourier Ψ (rectangle {i} t) = a * fourier g (setIndex t) := by
  by_cases ht : Odd t.card
  · have he := congrArg (fun F => fourier F (rectangle {i} t)) (funext (hp i))
    rw [fourier_average_translate, fourier_const_mul,
      ← rowIndex_setIndex, fourier_rowLift] at he
    have hav : average (fun σ : Cube m => sign (σ i) *
        character (rowIndex i (setIndex t)) (rowCube σ)) = 1 := by
      simp_rw [rowIndex_setIndex, character_rectangle_row _ _ ht, character_setIndex,
        Finset.prod_singleton, sign_sq]
      simp [average, smul_eq_mul]
    rw [hav, mul_one] at he
    simpa only [rowIndex_setIndex] using he
  · have ht' := Nat.not_odd_iff_even.mp ht
    rw [odd_even_coefficient_zero hΨ (by simpa [paritySign_rectangle] using ht'.neg_one_pow (α := ℝ)),
      odd_even_coefficient_zero hg (by rw [paritySign_setIndex]; exact ht'.neg_one_pow)]
    simp

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.row_rectangle_coefficient := @_root_.OAI.Cotype.row_rectangle_coefficient
