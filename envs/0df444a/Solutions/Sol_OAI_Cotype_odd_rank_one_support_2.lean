-- Prove2me | solution 2 for OAI.Cotype.odd_rank_one_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:03:22.232476+00:00
-- url     : https://prove2.me/submissions/0122ed43-415d-4723-8388-567d73887a1d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/BinaryRank.lean:L65-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.odd_rank_one_support. The node keeps its source
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

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem cross_eq_of_rank_le_one (A : Matrix ι κ (ZMod 2)) (hA : A.rank ≤ 1)
    (i i₀ : ι) (j j₀ : κ) : A i j * A i₀ j₀ = A i j₀ * A i₀ j := by
  let B : Matrix (Fin 2) (Fin 2) (ZMod 2) := A.submatrix ![i, i₀] ![j, j₀]
  have hr : B.rank ≤ 1 := (Matrix.rank_submatrix_le A _ _).trans hA
  by_contra h
  have hd : B.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    exact sub_ne_zero.mpr h
  have hh := Matrix.rank_of_det_ne_zero hd
  have : B.rank = 2 := by simpa using hh
  omega

theorem binary_rank_le_one_rectangle {P : (ι × κ) → Bool}
    (hP : (binaryMatrix P).rank ≤ 1) (hne : ∃ ij, P ij = true) :
    ∃ (s : Finset ι) (t : Finset κ), s.Nonempty ∧ t.Nonempty ∧ rectangle s t = P := by
  obtain ⟨⟨i₀,j₀⟩, h₀⟩ := hne
  let s := Finset.univ.filter (fun i => P (i,j₀) = true)
  let t := Finset.univ.filter (fun j => P (i₀,j) = true)
  refine ⟨s, t, ⟨i₀, by simp [s, h₀]⟩, ⟨j₀, by simp [t, h₀]⟩, ?_⟩
  funext ij
  obtain ⟨i,j⟩ := ij
  have hc := cross_eq_of_rank_le_one (binaryMatrix P) hP i i₀ j j₀
  simp only [binaryMatrix, h₀, ite_true, mul_one] at hc
  simp only [rectangle, s, t, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : P (i,j) <;> cases hi : P (i,j₀) <;> cases hj : P (i₀,j) <;>
    simp_all

theorem paritySign_rectangle (s : Finset ι) (t : Finset κ) :
    paritySign (rectangle s t) = (-1 : ℝ) ^ (s.card * t.card) := by
  rw [paritySign_eq]
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  rw [he, Finset.card_product]

theorem odd_rank_one_support {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f)
    {P : (ι × κ) → Bool} (hcoef : fourier f P ≠ 0)
    (hP : (binaryMatrix P).rank ≤ 1) :
    ∃ (s : Finset ι) (t : Finset κ),
      Odd s.card ∧ Odd t.card ∧ rectangle s t = P := by
  have hpar : paritySign P ≠ 1 := fun hp => hcoef (odd_even_coefficient_zero hf hp)
  have hne : ∃ ij, P ij = true := by
    by_contra h
    have hz (ij) : P ij = false := by
      cases hp : P ij <;> simp_all
    exact hpar (by simp [paritySign, hz])
  obtain ⟨s, t, _, _, he⟩ := binary_rank_le_one_rectangle hP hne
  have ho : Odd (s.card * t.card) := by
    by_contra h
    have heven := Nat.not_odd_iff_even.mp h
    apply hpar
    rw [← he, paritySign_rectangle]
    exact heven.neg_one_pow
  exact ⟨s, t, (Nat.odd_mul.mp ho).1, (Nat.odd_mul.mp ho).2, he⟩

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.odd_rank_one_support := @_root_.OAI.Cotype.odd_rank_one_support
