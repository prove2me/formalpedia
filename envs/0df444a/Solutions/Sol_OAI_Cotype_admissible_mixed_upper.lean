-- Prove2me | solution 1 for OAI.Cotype.admissible_mixed_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:03:05.67499+00:00
-- url     : https://prove2.me/submissions/e4d9ef9b-94f2-48c8-88e9-a17ffcaa310f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/MixedDerivative.lean:L108-L157
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.admissible_mixed_upper. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_chebyshevTruncation_bound
import Theorems.Thm_OAI_Cotype_deletedTail_bound
import Theorems.Thm_OAI_Cotype_exists_chebyshevExpansion
import Theorems.Thm_OAI_Cotype_fourier_inversion
import Theorems.Thm_OAI_Cotype_fourier_oddPart
import Theorems.Thm_OAI_Cotype_grouped_vector_generating
import Theorems.Thm_OAI_Cotype_odd_rank_one_support
import Theorems.Thm_OAI_Cotype_rectangle_injective_nonempty
import Theorems.Thm_OAI_Cotype_row_rectangle_coefficient
import Theorems.Thm_OAI_Cotype_splitHighU_degree

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

-- ---- from OAI.Analysis.Cotype.Rectangles ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem mem_rectangularIndices {k l : ℕ} {P : (ι × κ) → Bool} :
    P ∈ rectangularIndices k l ↔
      ∃ (s : Finset ι) (t : Finset κ), s.card = k ∧ t.card = l ∧ rectangle s t = P := by
  simp [rectangularIndices, Finset.mem_powersetCard, and_assoc]

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

-- ---- from OAI.Analysis.Cotype.BiasedFourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem biasedExpectation_const_mul (f : (ι → Bool) → ℝ) (t : ι → ℝ) (a : ℝ) :
    biasedExpectation (fun ε => a * f ε) t = a * biasedExpectation f t := by
  simp only [biasedExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  ring

theorem biasedExpectation_mul_const (f : (ι → Bool) → ℝ) (t : ι → ℝ) (a : ℝ) :
    biasedExpectation (fun ε => f ε * a) t = biasedExpectation f t * a := by
  simpa only [mul_comm] using biasedExpectation_const_mul f t a

theorem biasedExpectation_sum {α : Type*} [Fintype α]
    (f : α → (ι → Bool) → ℝ) (t : ι → ℝ) :
    biasedExpectation (fun ε => ∑ a, f a ε) t = ∑ a, biasedExpectation (f a) t := by
  simp only [biasedExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem biasWeight_sum (t : ι → ℝ) : (∑ ε, biasWeight t ε) = 1 := by
  unfold biasWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) => (1 + t i * sign b) / 2)]
  have he (i) : (∑ b : Bool, (1 + t i * sign b) / 2) = (1 : ℝ) := by
    simp only [Fintype.sum_bool, sign_true, sign_false]
    ring
  simp_rw [he]
  simp

omit [DecidableEq ι] in
theorem biasWeight_nonneg {t : ι → ℝ} (ht : ∀ i, |t i| ≤ 1) (ε : ι → Bool) :
    0 ≤ biasWeight t ε := by
  apply Finset.prod_nonneg
  intro i _
  obtain ⟨hl, hu⟩ := abs_le.mp (ht i)
  cases ε i <;> simp only [sign_false, sign_true] <;> linarith

theorem biasedExpectation_bound {f : (ι → Bool) → ℝ} {t : ι → ℝ} {M : ℝ}
    (ht : ∀ i, |t i| ≤ 1) (hf : ∀ ε, |f ε| ≤ M) :
    |biasedExpectation f t| ≤ M := by
  unfold biasedExpectation
  calc
    _ ≤ ∑ ε, |biasWeight t ε * f ε| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ε, biasWeight t ε * |f ε| := by
      apply Finset.sum_congr rfl
      intro ε _
      rw [abs_mul, abs_of_nonneg (biasWeight_nonneg ht ε)]
    _ ≤ ∑ ε, biasWeight t ε * M := Finset.sum_le_sum (fun ε _ =>
      mul_le_mul_of_nonneg_left (hf ε) (biasWeight_nonneg ht ε))
    _ = M := by rw [← Finset.sum_mul, biasWeight_sum, one_mul]

theorem biasedExpectation_character (t : ι → ℝ) (p : ι → Bool) :
    biasedExpectation (character p) t = ∏ i, if p i then t i else 1 := by
  unfold biasedExpectation biasWeight character
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    ((1 + t i * sign b) / 2) * (if p i then sign b else 1))]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp only [Fintype.sum_bool, sign_false, sign_true, Bool.false_eq_true,
    ite_false, ite_true] <;> ring

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

theorem character_rectangle_column (s : Finset ι) (t : Finset κ)
    (hs : Odd s.card) (τ : κ → Bool) :
    character (rectangle s t) (columnCube τ) = character (setIndex t) τ := by
  rw [character_rectangle, Finset.prod_comm, character_setIndex]
  apply Finset.prod_congr rfl
  intro j _
  simp only [columnCube, Finset.prod_const]
  cases τ j <;> simp [hs.neg_one_pow]

theorem biasedExpectation_setIndex (s : Finset ι) (a : ℝ) :
    biasedExpectation (character (setIndex s)) (fun _ => a) = a ^ s.card := by
  rw [biasedExpectation_character]
  simp [setIndex]

theorem biasedExpectation_rectangle (s : Finset ι) (t : Finset κ) (c : ℝ) :
    biasedExpectation (character (rectangle s t)) (fun _ => c) = c ^ (s.card * t.card) := by
  rw [biasedExpectation_character]
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  rw [← Finset.prod_filter, he]
  simp

theorem dampedExpectation_bound {f : ((ι × κ) → Bool) → ℝ} {M a b c : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hf : ∀ S, |f S| ≤ M) :
    |dampedExpectation f a b c| ≤ M := by
  apply biasedExpectation_bound (fun _ => ha)
  intro σ
  apply biasedExpectation_bound (fun _ => hb)
  intro τ
  exact biasedExpectation_bound (fun _ => hc) (fun R => hf (dampedSample σ τ R))

theorem dampedExpectation_odd_rectangle (s : Finset ι) (t : Finset κ)
    (hs : Odd s.card) (ht : Odd t.card) (a b c : ℝ) :
    dampedExpectation (character (rectangle s t)) a b c =
      a ^ s.card * b ^ t.card * c ^ (s.card * t.card) := by
  unfold dampedExpectation dampedSample
  simp_rw [character_xor, character_rectangle_row s t ht, character_rectangle_column s t hs]
  simp_rw [biasedExpectation_const_mul, biasedExpectation_mul_const,
    biasedExpectation_rectangle, biasedExpectation_setIndex]
  ring

theorem dampedExpectation_fourier (f : ((ι × κ) → Bool) → ℝ) (a b c : ℝ) :
    dampedExpectation f a b c =
      ∑ P, fourier f P * dampedExpectation (character P) a b c := by
  calc
    dampedExpectation f a b c = dampedExpectation
        (fun S => ∑ P, fourier f P * character P S) a b c := by
      congr 1
      funext S
      exact (fourier_inversion f S).symm
    _ = _ := by
      simp only [dampedExpectation]
      simp_rw [biasedExpectation_sum, biasedExpectation_const_mul]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GroupedPolynomial ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectangle_mem_rectangularIndices {s : Finset ι} {t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (k l : ℕ) :
    rectangle s t ∈ rectangularIndices k l ↔ k = s.card ∧ l = t.card := by
  rw [mem_rectangularIndices]
  constructor
  · rintro ⟨s', t', hk, hl, he⟩
    obtain ⟨rfl, rfl⟩ := rectangle_injective_nonempty hs ht he.symm
    exact ⟨hk.symm, hl.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨s, t, rfl, rfl, rfl⟩

theorem Ckl_eq_sum_univ (f : ((ι × κ) → Bool) → ℝ) (k l : ℕ) :
    Ckl f k l = ∑ P, if P ∈ rectangularIndices k l then fourier f P else 0 := by
  simp [Ckl]

theorem groupedPolynomial_eq_expectation {f : ((ι × κ) → Bool) → ℝ}
    (hf : IsOdd f) (hr : RankOneSupported f) (a b c : ℝ) :
    groupedPolynomial f a b c = dampedExpectation f a b c := by
  rw [dampedExpectation_fourier]
  unfold groupedPolynomial
  simp_rw [Ckl_eq_sum_univ, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hz : fourier f P = 0
  · simp [hz]
  obtain ⟨s, t, hs, ht, he⟩ := odd_rank_one_support hf hz (hr P hz)
  have hsne : s.Nonempty := Finset.card_pos.mp (by obtain ⟨k, hk⟩ := hs; omega)
  have htne : t.Nonempty := Finset.card_pos.mp (by obtain ⟨k, hk⟩ := ht; omega)
  have hsc : s.card < Fintype.card ι + 1 := Nat.lt_succ_of_le (Finset.card_le_univ s)
  have htc : t.card < Fintype.card κ + 1 := Nat.lt_succ_of_le (Finset.card_le_univ t)
  rw [← he, dampedExpectation_odd_rectangle s t hs ht]
  simp_rw [rectangle_mem_rectangularIndices hsne htne]
  simp [ite_and, hsc, htc, mul_assoc]

theorem groupedPolynomial_bound {f : ((ι × κ) → Bool) → ℝ} {M a b : ℝ}
    (hf : IsOdd f) (hr : RankOneSupported f) (hM : ∀ S, |f S| ≤ M)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |groupedPolynomial f a b (1/2)| ≤ M := by
  rw [groupedPolynomial_eq_expectation hf hr]
  exact dampedExpectation_bound ha hb (by norm_num) hM

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionCoefficients ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem paritySign_setIndex (t : Finset ι) : paritySign (setIndex t) = (-1 : ℝ)^t.card := by
  simp [paritySign_eq, setIndex]

omit [DecidableEq ι] [DecidableEq κ] in
theorem character_transpose (P S : (ι × κ) → Bool) :
    character (transposeCube P) (transposeCube S) = character P S := by
  simp only [character, Fintype.prod_prod_type, transposeCube]
  exact Finset.prod_comm

theorem fourier_transpose (f : ((ι × κ) → Bool) → ℝ) (P : (ι × κ) → Bool) :
    fourier (fun S => f (transposeCube S)) (transposeCube P) = fourier f P := by
  simp only [fourier, average, smul_eq_mul]
  have hc : Fintype.card ((κ × ι) → Bool) = Fintype.card ((ι × κ) → Bool) :=
    Fintype.card_congr transposeEquiv.symm
  rw [hc]
  congr 1
  exact Fintype.sum_equiv transposeEquiv.symm _ _ (fun S => by
    exact congrArg (fun z => f (transposeCube S) * z)
      (character_transpose P (transposeCube S)))

omit [Fintype ι] [Fintype κ] in
theorem transpose_rectangle (s : Finset ι) (t : Finset κ) :
    transposeCube (rectangle s t) = rectangle t s := by
  funext ij
  simp [transposeCube, rectangle, and_comm]

theorem column_rectangle_coefficient {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {f : Cube m → ℝ} {b : ℝ} (hΨ : IsOdd Ψ) (hf : IsOdd f)
    (hp : ∀ (j : Fin n) S, average (fun τ : Cube n =>
      sign (τ j) * Ψ (xorCube (columnCube τ) S)) = b * f (fun i => S (i,j)))
    (s : Finset (Fin m)) (j : Fin n) :
    fourier Ψ (rectangle s {j}) = b * fourier f (setIndex s) := by
  have ho : IsOdd (fun S => Ψ (transposeCube S)) := fun S => hΨ (transposeCube S)
  have hproj : ∀ (j : Fin n) S, average (fun τ : Cube n =>
      sign (τ j) * Ψ (transposeCube (xorCube (rowCube τ) S))) =
        b * f (fun i => S (j,i)) := fun j S => hp j (transposeCube S)
  have h := row_rectangle_coefficient ho hf hproj j s
  rw [← transpose_rectangle s {j}, fourier_transpose] at h
  exact h

theorem Ckl_pair_sum (f : ((ι × κ) → Bool) → ℝ) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    Ckl f k l = ∑ s ∈ Finset.univ.powersetCard k, ∑ t ∈ Finset.univ.powersetCard l,
      fourier f (rectangle s t) := by
  unfold Ckl rectangularIndices
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro st hst st' hst' he
    have hs : st.1.Nonempty := Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp (Finset.mem_product.mp hst).1).2]; exact hk)
    have ht : st.2.Nonempty := Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp (Finset.mem_product.mp hst).2).2]; exact hl)
    exact Prod.ext (rectangle_injective_nonempty hs ht he).1
      (rectangle_injective_nonempty hs ht he).2

theorem Ckl_zero_right {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f) (k : ℕ) :
    Ckl f k 0 = 0 := by
  apply Finset.sum_eq_zero
  intro P hP
  obtain ⟨s, t, _, ht, rfl⟩ := mem_rectangularIndices.mp hP
  rw [Finset.card_eq_zero.mp ht]
  exact odd_even_coefficient_zero hf (by simp [paritySign_rectangle])

theorem Ckl_zero_left {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f) (l : ℕ) :
    Ckl f 0 l = 0 := by
  apply Finset.sum_eq_zero
  intro P hP
  obtain ⟨s, t, hs, _, rfl⟩ := mem_rectangularIndices.mp hP
  rw [Finset.card_eq_zero.mp hs]
  exact odd_even_coefficient_zero hf (by simp [paritySign_rectangle])

theorem levelFourier_zero {g : (ι → Bool) → ℝ} (hg : IsOdd g) : levelFourier g 0 = 0 := by
  simp only [levelFourier, Finset.powersetCard_zero, Finset.sum_singleton]
  exact odd_even_coefficient_zero hg (by simp [paritySign_setIndex])

theorem Ckl_one_row {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {g : Cube n → ℝ} {a : ℝ} (hΨ : IsOdd Ψ) (hg : IsOdd g)
    (hp : ∀ (i : Fin m) S, average (fun σ : Cube m =>
      sign (σ i) * Ψ (xorCube (rowCube σ) S)) = a * g (fun j => S (i,j)))
    (l : ℕ) : Ckl Ψ 1 l = (m : ℝ)*a*levelFourier g l := by
  by_cases hl : l = 0
  · simp [hl, Ckl_zero_right hΨ, levelFourier_zero hg]
  rw [Ckl_pair_sum Ψ (by omega) (by omega), Finset.powersetCard_one]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  simp_rw [row_rectangle_coefficient hΨ hg hp]
  simp [levelFourier, ← Finset.mul_sum, mul_assoc]

theorem Ckl_one_column {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {f : Cube m → ℝ} {b : ℝ} (hΨ : IsOdd Ψ) (hf : IsOdd f)
    (hp : ∀ (j : Fin n) S, average (fun τ : Cube n =>
      sign (τ j) * Ψ (xorCube (columnCube τ) S)) = b * f (fun i => S (i,j)))
    (k : ℕ) : Ckl Ψ k 1 = (n : ℝ)*b*levelFourier f k := by
  by_cases hk : k = 0
  · simp [hk, Ckl_zero_left hΨ, levelFourier_zero hf]
  rw [Ckl_pair_sum Ψ (by omega) (by omega), Finset.powersetCard_one]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk,
    column_rectangle_coefficient hΨ hf hp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [mul_assoc, ← Finset.mul_sum, levelFourier]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.DeletedTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem cutoff_power_bound {m : ℕ} (hd : 4 ≤ degreeCutoff m)
    (hm : degreeCutoff m < m) : (m : ℝ) ≤ (2 : ℝ) ^ (degreeCutoff m - 2) := by
  have hc : 2 * Real.logb 2 (m : ℝ) ≤ (degreeCutoff m : ℝ) := Nat.le_ceil _
  have hsub : ((degreeCutoff m - 2 : ℕ) : ℝ) = (degreeCutoff m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hl : Real.logb 2 (m : ℝ) ≤ ((degreeCutoff m - 2 : ℕ) : ℝ) := by
    rw [hsub]
    have hd' : (4 : ℝ) ≤ degreeCutoff m := by exact_mod_cast hd
    linarith
  have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  simpa only [Real.rpow_natCast] using
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).mp hl

variable {m : ℕ}

theorem grouped_sub_truncated (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    groupedPolynomial f s u (1/2) - truncatedGrouped f d s u = deletedTail f d s u := by
  simp only [groupedPolynomial, Fintype.card_fin, truncatedGrouped, deletedTail,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hk : k ≤ d <;> by_cases hl : l ≤ d <;> simp [hk, hl]

theorem truncatedGrouped_bound {f : SignMatrix m → ℝ} {M s u : ℝ}
    (ho : IsOdd f) (hr : RankOneSupported f) (hM : 0 ≤ M)
    (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |truncatedGrouped f (degreeCutoff m) s u| ≤ 2*M := by
  have he := grouped_sub_truncated f (degreeCutoff m) s u
  have hh := groupedPolynomial_bound ho hr hf hs hu
  have ht := deletedTail_bound hM hf hd (cutoff_power_bound hd hm) hs hu
  rw [show truncatedGrouped f (degreeCutoff m) s u =
    groupedPolynomial f s u (1/2) - deletedTail f (degreeCutoff m) s u by linarith]
  exact (abs_sub _ _).trans (by linarith)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ChebyshevBounds ----
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev MeasureTheory
namespace Cotype

theorem chebyshev_derivative_zero_bound (n : ℕ) :
    |(T ℝ n).derivative.eval 0| ≤ n := by
  have hU := U_real_cos (Real.pi / 2) ((n : ℤ) - 1)
  have hUn : |(U ℝ ((n : ℤ)-1)).eval 0| ≤ 1 := by
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_one] at hU
    rw [hU]
    exact Real.abs_sin_le_one _
  rw [T_derivative_eq_U]
  simp only [eval_mul, Int.cast_natCast, eval_natCast, abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact (mul_le_mul_of_nonneg_left hUn (Nat.cast_nonneg n)).trans_eq (mul_one _)

theorem chebyshev_pairing_bound (Q : ℝ[X]) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) :
    |∫ x, Q.eval x * (T ℝ n).eval x ∂measureT| ≤ M * Real.pi := by
  rw [integral_measureT_eq_integral_cos]
  have hh : ∀ θ ∈ Set.uIoc (0 : ℝ) Real.pi,
      ‖Q.eval (Real.cos θ) * (T ℝ n).eval (Real.cos θ)‖ ≤ M := by
    intro θ _
    rw [Real.norm_eq_abs, abs_mul, T_real_cos]
    exact (mul_le_mul (hQ _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
      (Real.abs_cos_le_one _) (abs_nonneg _) hM).trans_eq (mul_one M)
  simpa [Real.norm_eq_abs, abs_of_pos Real.pi_pos] using
    intervalIntegral.norm_integral_le_of_norm_le_const hh

theorem chebyshev_pairing (i j : ℕ) :
    (∫ x, (T ℝ i).eval x * (T ℝ j).eval x ∂measureT) =
      if i = j then (if j = 0 then Real.pi else Real.pi/2) else 0 := by
  by_cases hij : i = j
  · subst i
    by_cases hj : j = 0
    · subst j
      simpa using integral_eval_T_real_mul_self_measureT_zero
    · simpa [hj] using integral_T_real_mul_self_measureT_of_ne_zero hj
  · simpa [hij] using integral_eval_T_real_mul_eval_T_real_measureT_of_ne hij

theorem chebyshevExpansion_pairing {d : ℕ} (c : Fin (d+1) → ℝ) (j : Fin (d+1)) :
    (∫ x, (chebyshevExpansion c).eval x * (T ℝ (j : ℕ)).eval x ∂measureT) =
      c j * (if (j : ℕ) = 0 then Real.pi else Real.pi/2) := by
  simp only [chebyshevExpansion, eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [mul_assoc, MeasureTheory.integral_const_mul, chebyshev_pairing]
    simp only [Fin.val_inj]
    simp
  · intro i _
    exact integrable_measureT (by fun_prop)

theorem chebyshevExpansion_coefficient_bound {d : ℕ} (c : Fin (d+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    (j : Fin (d+1)) : |c j| ≤ 2*M := by
  have hh := chebyshev_pairing_bound (chebyshevExpansion c) j hM hQ
  rw [chebyshevExpansion_pairing, abs_mul] at hh
  split_ifs at hh
  · rw [abs_of_pos Real.pi_pos] at hh
    nlinarith [Real.pi_pos]
  · rw [abs_of_pos (by positivity : 0 < Real.pi/2)] at hh
    nlinarith [Real.pi_pos]

theorem sum_fin_cast (d : ℕ) :
    (∑ j : Fin (d+1), (j : ℝ)) = (d : ℝ) * (d+1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem chebyshevExpansion_derivative_bound {d : ℕ} (c : Fin (d+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M) :
    |(chebyshevExpansion c).derivative.eval 0| ≤ (d : ℝ) * (d+1) * M := by
  have he : (chebyshevExpansion c).derivative.eval 0 =
      ∑ j : Fin (d+1), c j * (T ℝ (j : ℕ)).derivative.eval 0 := by
    simp [chebyshevExpansion, eval_finsetSum]
  rw [he]
  calc
    _ ≤ ∑ j : Fin (d+1), |c j * (T ℝ (j : ℕ)).derivative.eval 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (d+1), (2*M) * (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (chebyshevExpansion_coefficient_bound c hM hQ j)
        (chebyshev_derivative_zero_bound j) (abs_nonneg _) (by positivity)
    _ = (d : ℝ) * (d+1) * M := by
      rw [← Finset.mul_sum, sum_fin_cast]
      ring

theorem polynomial_derivative_zero_bound (Q : ℝ[X]) (d : ℕ) (hdeg : Q.degree ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) :
    |Q.derivative.eval 0| ≤ (d : ℝ) * (d+1) * M := by
  obtain ⟨c, rfl⟩ := exists_chebyshevExpansion Q d hdeg
  exact chebyshevExpansion_derivative_bound c hM hQ

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.BivariateSplit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
namespace Cotype

theorem chebLow_degree (d : ℕ) (Q : ℝ[X]) : (chebLow d Q).degree ≤ d := by
  change (∑ j ∈ Finset.range (d+1), (chebBasis.repr Q) j • T ℝ j).degree ≤ d
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j hj
  apply (degree_smul_le _ _).trans
  have hd := (chebyshevTsequence ℝ).degree_eq j
  change (T ℝ j).degree = (j : WithBot ℕ) at hd
  rw [hd]
  exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)

theorem chebLow_eq_self {d : ℕ} {Q : ℝ[X]} (hQ : Q.degree ≤ d) : chebLow d Q = Q := by
  obtain ⟨c, rfl⟩ := exists_chebyshevExpansion Q d hQ
  simp only [chebyshevExpansion, map_sum, map_smul, chebLow_basis]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (Nat.le_of_lt_succ j.isLt)]

theorem chebLow_expansion {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ) :
    chebLow d (chebyshevExpansion c) = chebyshevTruncation c d := by
  simp only [chebyshevExpansion, map_sum, map_smul, chebLow_basis, chebyshevTruncation,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem chebLow_bound (Q : ℝ[X]) (d : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebLow d Q).eval x| ≤ 2*M*(d+1) := by
  obtain ⟨c, hc⟩ := exists_chebyshevExpansion Q Q.natDegree (degree_le_natDegree)
  rw [← hc, chebLow_expansion]
  exact chebyshevTruncation_bound c d hM (by simpa [hc] using hQ) hx

variable {m : ℕ}

theorem retainedSectionS_eval (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    (retainedSectionS f d u).eval s = truncatedGrouped f d s u := by
  simp only [retainedSectionS, eval_finsetSum, eval_smul, smul_eq_mul, eval_pow,
    eval_X, truncatedGrouped]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  unfold retainedCoefficient
  split_ifs <;> ring

theorem bivariate_split_eval (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    truncatedGrouped f d s u = (splitLowS f d u).eval s + (splitHighU f d s).eval u := by
  rw [← retainedSectionS_eval f d s u]
  simp only [splitLowS, retainedSectionS, splitHighU, map_sum, map_smul,
    eval_finsetSum, eval_smul, smul_eq_mul, eval_sub, eval_pow, eval_X,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem splitLowS_degree (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) :
    (splitLowS f d u).degree ≤ d := chebLow_degree d _

theorem splitLowS_bound {f : SignMatrix m → ℝ} {M s u : ℝ}
    (ho : IsOdd f) (hr : RankOneSupported f) (hM : 0 ≤ M)
    (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |(splitLowS f (degreeCutoff m) u).eval s| ≤ 4*M*(degreeCutoff m+1) := by
  have hh : ∀ x ∈ Set.Icc (-1) 1,
      |(retainedSectionS f (degreeCutoff m) u).eval x| ≤ 2*M := by
    intro x hx
    rw [retainedSectionS_eval]
    exact truncatedGrouped_bound ho hr hM hf hd hm (abs_le.mpr hx) hu
  have h := chebLow_bound (retainedSectionS f (degreeCutoff m) u) (degreeCutoff m)
    (by positivity : 0 ≤ 2*M) hh (abs_le.mp hs)
  dsimp [splitLowS]
  nlinarith

theorem splitHighU_bound {f : SignMatrix m → ℝ} {M s u : ℝ}
    (ho : IsOdd f) (hr : RankOneSupported f) (hM : 0 ≤ M)
    (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |(splitHighU f (degreeCutoff m) s).eval u| ≤ 6*M*(degreeCutoff m+1) := by
  have he := bivariate_split_eval f (degreeCutoff m) s u
  have h0 := truncatedGrouped_bound ho hr hM hf hd hm hs hu
  have h1 := splitLowS_bound ho hr hM hf hd hm hs hu
  have ha := abs_sub (truncatedGrouped f (degreeCutoff m) s u)
    ((splitLowS f (degreeCutoff m) u).eval s)
  rw [show truncatedGrouped f (degreeCutoff m) s u -
    (splitLowS f (degreeCutoff m) u).eval s = (splitHighU f (degreeCutoff m) s).eval u by linarith] at ha
  nlinarith [mul_nonneg hM (Nat.cast_nonneg (α := ℝ) (degreeCutoff m))]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionDerivatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {m : ℕ}

theorem derivative_eval_zero (Q : ℝ[X]) : Q.derivative.eval 0 = Q.coeff 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  norm_num

theorem partialS_eq (f : SignMatrix m → ℝ) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    partialS f d = ∑ l ∈ Finset.range (m+1), (Ckl f 1 l * (1/2 : ℝ)^l) • X^l := by
  simp only [partialS, derivative_eval_zero, coeff_X_pow, eq_comm]
  have he (k l : ℕ) : (retainedCoefficient f d k l * (if k = 1 then (1:ℝ) else 0)) • (X : ℝ[X])^l =
      if k = 1 then (Ckl f 1 l * (1/2 : ℝ)^l) • X^l else 0 := by
    split_ifs with h
    · subst k; simp [retainedCoefficient, hd]
    · simp
  simp_rw [he]
  simp [Finset.sum_ite_eq', show 1 < m+1 by omega]

theorem partialU_eq (f : SignMatrix m → ℝ) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    partialU f d = ∑ k ∈ Finset.range (m+1), (Ckl f k 1 * (1/2 : ℝ)^k) • X^k := by
  simp only [partialU, derivative_eval_zero, coeff_X_pow, eq_comm]
  have he (k l : ℕ) : (retainedCoefficient f d k l * (if l = 1 then (1:ℝ) else 0)) • (X : ℝ[X])^k =
      if l = 1 then (Ckl f k 1 * (1/2 : ℝ)^k) • X^k else 0 := by
    split_ifs with h
    · subst l; simp [retainedCoefficient, hd]
    · simp
  simp_rw [he]
  simp [Finset.sum_ite_eq', show 1 < m+1 by omega]

theorem admissible_partialS {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (u : ℝ) :
    (partialS Ψ d).eval u = (m : ℝ)*a * biasedExpectation g (fun _ => u/2) := by
  obtain ⟨hΨ, _, hg, _, _, _, _, _, hp, _⟩ := h
  rw [partialS_eq Ψ hd hm]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, eval_pow, eval_X,
    Ckl_one_row hΨ hg hp]
  rw [← grouped_vector_generating]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [div_eq_mul_inv, mul_pow]
  ring

theorem admissible_partialU {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (s : ℝ) :
    (partialU Ψ d).eval s = (m : ℝ)*b * biasedExpectation f (fun _ => s/2) := by
  obtain ⟨hΨ, hf, _, _, _, _, _, _, _, hp⟩ := h
  rw [partialU_eq Ψ hd hm]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, eval_pow, eval_X,
    Ckl_one_column hΨ hf hp]
  rw [← grouped_vector_generating]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_eq_mul_inv, mul_pow]
  ring

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.MixedDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace Cotype

variable {m : ℕ}

theorem lowPartialS_eval (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) :
    (lowPartialS f d).eval u = (splitLowS f d u).derivative.eval 0 := by
  simp only [lowPartialS, splitLowS, retainedSectionS, map_sum, map_smul,
    eval_finsetSum, eval_smul, smul_eq_mul,
    eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem highPartialS_sum (f : SignMatrix m → ℝ) (d : ℕ) :
    highPartialS f d = ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
      (retainedCoefficient f d k l *
        (((X : ℝ[X])^k - chebLow d (X^k)).derivative.eval 0)) • X^l := by
  simp only [highPartialS, partialS, lowPartialS, ← Finset.sum_sub_distrib,
    derivative_sub, eval_sub]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [← sub_smul, ← mul_sub]

theorem highPartialS_degree (f : SignMatrix m → ℝ) (d : ℕ) :
    (highPartialS f d).degree ≤ d := by
  rw [highPartialS_sum]
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro k _
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro l _
  by_cases hk : k ≤ d
  · have he : chebLow d ((X : ℝ[X])^k) = X^k := chebLow_eq_self (by simpa using hk)
    simp [he]
  · by_cases hl : l ≤ d
    · apply (degree_smul_le _ _).trans
      simpa using hl
    · simp [retainedCoefficient, hk, hl]

theorem highPartialU_eval (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) :
    (partialU f d - chebLow d (partialU f d)).eval s =
      (splitHighU f d s).derivative.eval 0 := by
  simp only [partialU, splitHighU, map_sum, map_smul, ← Finset.sum_sub_distrib,
    eval_finsetSum, eval_sub, eval_smul, smul_eq_mul,
    eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem mixed_split (f : SignMatrix m → ℝ) (d : ℕ) :
    (partialS f d).derivative.eval 0 =
      (chebLow d (partialU f d)).derivative.eval 0 + (highPartialS f d).derivative.eval 0 := by
  have he : (lowPartialS f d).derivative.eval 0 = (chebLow d (partialU f d)).derivative.eval 0 := by
    simp only [lowPartialS, partialU, map_sum, map_smul,
      eval_finsetSum, eval_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [highPartialS, derivative_sub, eval_sub]
  linarith

theorem admissible_partialS_bound {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (ha : 0 ≤ a) {d : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) {u : ℝ} (hu : |u| ≤ 1) :
    |(partialS Ψ d).eval u| ≤ (m : ℝ)*a*4 := by
  rw [admissible_partialS h hd hm]
  obtain ⟨_, _, _, _, _, hgM, _, _, _, _⟩ := h
  have hmean : |u/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ha)]
  exact mul_le_mul_of_nonneg_left (biasedExpectation_bound (fun _ => hmean) hgM)
    (mul_nonneg (Nat.cast_nonneg _) ha)

theorem admissible_partialU_bound {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (hb : 0 ≤ b) {d : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) {s : ℝ} (hs : |s| ≤ 1) :
    |(partialU Ψ d).eval s| ≤ (m : ℝ)*b*4 := by
  rw [admissible_partialU h hd hm]
  obtain ⟨_, _, _, _, hfM, _, _, _, _, _⟩ := h
  have hmean : |s/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb)]
  exact mul_le_mul_of_nonneg_left (biasedExpectation_bound (fun _ => hmean) hfM)
    (mul_nonneg (Nat.cast_nonneg _) hb)

theorem admissible_mixed_upper {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (hr : RankOneSupported Ψ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m) :
    |(partialS Ψ (degreeCutoff m)).derivative.eval 0| ≤
      4 * (degreeCutoff m : ℝ) * (degreeCutoff m+1) *
        ((m : ℝ)*a + (m : ℝ)*b + 10*(degreeCutoff m : ℝ)*(degreeCutoff m+1)^2) := by
  let d := degreeCutoff m
  have hd1 : 1 ≤ d := by dsimp [d]; omega
  have hm1 : 1 ≤ m := by omega
  have hΨ := h.1
  have hM : ∀ S, |Ψ S| ≤ 4 := h.2.2.2.1
  have hlo (u : ℝ) (hu : |u| ≤ 1) :
      |(lowPartialS Ψ d).eval u| ≤ 16*(d : ℝ)*(d+1)^2 := by
    rw [lowPartialS_eval]
    have hh := polynomial_derivative_zero_bound (splitLowS Ψ d u) d (splitLowS_degree Ψ d u)
      (by positivity : 0 ≤ 16*((d:ℝ)+1)) (fun s hs => by
        simpa only [show (4:ℝ)*4=16 by norm_num] using
          splitLowS_bound hΨ hr (by norm_num) hM hd hm (abs_le.mpr hs) hu)
    convert hh using 1; ring
  have hhi (s : ℝ) (hs : |s| ≤ 1) :
      |(partialU Ψ d - chebLow d (partialU Ψ d)).eval s| ≤ 24*(d : ℝ)*(d+1)^2 := by
    rw [highPartialU_eval]
    have hh := polynomial_derivative_zero_bound (splitHighU Ψ d s) d (splitHighU_degree Ψ d s)
      (by positivity : 0 ≤ 24*((d:ℝ)+1)) (fun u hu => by
        simpa only [show (6:ℝ)*4=24 by norm_num] using
          splitHighU_bound hΨ hr (by norm_num) hM hd hm hs (abs_le.mpr hu))
    convert hh using 1; ring
  have hhs (u : ℝ) (hu : |u| ≤ 1) :
      |(highPartialS Ψ d).eval u| ≤ (m : ℝ)*a*4 + 16*(d : ℝ)*(d+1)^2 := by
    simp only [highPartialS, eval_sub]
    exact (abs_sub _ _).trans (add_le_add (admissible_partialS_bound h ha hd1 hm1 hu) (hlo u hu))
  have hlu (s : ℝ) (hs : |s| ≤ 1) :
      |(chebLow d (partialU Ψ d)).eval s| ≤ (m : ℝ)*b*4 + 24*(d : ℝ)*(d+1)^2 := by
    have hh := hhi s hs
    simp only [eval_sub] at hh
    have hpu := admissible_partialU_bound h hb hd1 hm1 hs
    have he : (chebLow d (partialU Ψ d)).eval s =
        (partialU Ψ d).eval s - ((partialU Ψ d).eval s - (chebLow d (partialU Ψ d)).eval s) := by ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hpu hh)
  have hb1 := polynomial_derivative_zero_bound (highPartialS Ψ d) d (highPartialS_degree Ψ d)
    (by positivity : 0 ≤ (m:ℝ)*a*4 + 16*(d:ℝ)*(d+1)^2)
    (fun u hu => hhs u (abs_le.mpr hu))
  have hb2 := polynomial_derivative_zero_bound (chebLow d (partialU Ψ d)) d (chebLow_degree d _)
    (by positivity : 0 ≤ (m:ℝ)*b*4 + 24*(d:ℝ)*(d+1)^2)
    (fun s hs => hlu s (abs_le.mpr hs))
  rw [mixed_split]
  apply (abs_add_le _ _).trans
  have hh := add_le_add hb2 hb1
  convert hh using 1; dsimp [d]; ring

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open Polynomial


theorem solution : type_of% @_root_.OAI.Cotype.admissible_mixed_upper := @_root_.OAI.Cotype.admissible_mixed_upper
