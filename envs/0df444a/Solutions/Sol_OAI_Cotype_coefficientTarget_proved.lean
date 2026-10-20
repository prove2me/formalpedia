-- Prove2me | solution 1 for OAI.Cotype.coefficientTarget_proved
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:08:48.668339+00:00
-- url     : https://prove2.me/submissions/82f708b3-fdfe-4679-9966-428b0d062de8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CoefficientCompactness.lean:L78-L96
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.coefficientTarget_proved. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_admissible_mixed_upper
import Theorems.Thm_OAI_Cotype_coefficient_numerical_contradiction
import Theorems.Thm_OAI_Cotype_fourier_oddPart
import Theorems.Thm_OAI_Cotype_rectangle_injective_nonempty
import Theorems.Thm_OAI_Cotype_row_rectangle_coefficient

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

-- ---- from OAI.Analysis.Cotype.ProjectionCoefficients ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem paritySign_setIndex (t : Finset ι) : paritySign (setIndex t) = (-1 : ℝ)^t.card := by
  simp [paritySign_eq, setIndex]

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

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionDerivatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {m : ℕ}

theorem levelFourier_first {g : Cube m → ℝ} {b : ℝ}
    (hb : ∀ j, fourier g (unitIndex j) = b) : levelFourier g 1 = (m : ℝ)*b := by
  have he (j : Fin m) : setIndex {j} = unitIndex j := by
    funext i; simp [setIndex, unitIndex, eq_comm]
  simp [levelFourier, Finset.powersetCard_one, he, hb]

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

theorem admissible_mixed_derivative {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (partialS Ψ d).derivative.eval 0 = ((m : ℝ)*a)*((m : ℝ)*b)/2 := by
  obtain ⟨hΨ, _, hg, _, _, _, _, hb, hp, _⟩ := h
  rw [derivative_eval_zero, partialS_eq Ψ hd hm]
  simp only [finsetSum_coeff, coeff_smul, coeff_X_pow, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  rw [ite_eq_left (Finset.mem_range.mpr (by omega))]
  rw [Ckl_one_row hΨ hg hp, levelFourier_first hb]
  norm_num
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

theorem admissible_exists_rank_two {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (ha : 0 < a) (hb : 0 < b)
    (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hlarge : 80*(degreeCutoff m : ℝ)*(degreeCutoff m+1)^2 ≤ min ((m:ℝ)*a) ((m:ℝ)*b)) :
    ∃ P : SignMatrix m, 2 ≤ (binaryMatrix P).rank ∧ fourier Ψ P ≠ 0 := by
  by_contra hn
  have hr : RankOneSupported Ψ := by
    intro P hP
    have hh : ¬ 2 ≤ (binaryMatrix P).rank := fun hh => hn ⟨P, hh, hP⟩
    omega
  have hu := admissible_mixed_upper h hr ha.le hb.le hd hm
  rw [admissible_mixed_derivative h (by omega) (by omega)] at hu
  rw [abs_of_nonneg (by positivity)] at hu
  exact coefficient_numerical_contradiction (by exact_mod_cast hd)
    (hlarge.trans (min_le_left _ _)) (hlarge.trans (min_le_right _ _)) hu

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CoefficientCompactness ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem admissibleSet_closed (m : ℕ) (a b : ℝ) : IsClosed (admissibleSet m a b) := by
  simp only [admissibleSet, ScalarAdmissible, IsOdd, fourier, average, smul_eq_mul,
    Set.ofPred_and, Set.ofPred_forall]
  repeat' first
    | apply IsClosed.inter
    | apply isClosed_iInter; intro i
  all_goals first
    | exact isClosed_le (by fun_prop) (by fun_prop)
    | exact isClosed_eq (by fun_prop) (by fun_prop)

theorem function_box_compact (α : Type*) :
    IsCompact {f : α → ℝ | ∀ x, |f x| ≤ 4} := by
  have h : IsCompact {f : α → ℝ | ∀ x, f x ∈ Set.Icc (-4 : ℝ) 4} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  simpa only [Set.mem_Icc, abs_le] using h

theorem admissibleSet_compact (m : ℕ) (a b : ℝ) : IsCompact (admissibleSet m a b) := by
  have hbox := (function_box_compact (SignMatrix m)).prod
    ((function_box_compact (Cube m)).prod (function_box_compact (Cube m)))
  apply hbox.of_isClosed_subset (admissibleSet_closed m a b)
  intro x hx
  obtain ⟨_, _, _, hΨ, hf, hg, _, _, _, _⟩ := hx
  exact ⟨hΨ, hf, hg⟩

variable {m : ℕ}

theorem rankTwoMax_continuous (m : ℕ) : Continuous (@rankTwoMax m) := by
  apply Continuous.finset_sup'_apply
  intro P _
  by_cases hP : 2 ≤ (binaryMatrix P).rank
  · simp only [ite_eq_left hP]
    unfold fourier average
    fun_prop
  · simp only [ite_eq_right hP]
    fun_prop

theorem rankTwoMax_pos {Ψ : SignMatrix m → ℝ}
    (h : ∃ P, 2 ≤ (binaryMatrix P).rank ∧ fourier Ψ P ≠ 0) : 0 < rankTwoMax Ψ := by
  obtain ⟨P, hP, hc⟩ := h
  have hle := Finset.le_sup' (s := (Finset.univ : Finset (SignMatrix m)))
    (f := fun Q => if 2 ≤ (binaryMatrix Q).rank then |fourier Ψ Q| else 0) (Finset.mem_univ P)
  rw [ite_eq_left hP] at hle
  exact (abs_pos.mpr hc).trans_le hle

theorem rankTwoMax_attained {Ψ : SignMatrix m → ℝ} (h : 0 < rankTwoMax Ψ) :
    ∃ P, 2 ≤ (binaryMatrix P).rank ∧ rankTwoMax Ψ = |fourier Ψ P| := by
  obtain ⟨P, _, hP⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (SignMatrix m)))
    Finset.univ_nonempty (fun P => if 2 ≤ (binaryMatrix P).rank then |fourier Ψ P| else 0)
  by_cases hr : 2 ≤ (binaryMatrix P).rank
  · exact ⟨P, hr, by simpa [rankTwoMax, hr] using hP⟩
  · have hz : rankTwoMax Ψ = 0 := by simpa [rankTwoMax, hr] using hP
    linarith

theorem coefficientTarget_proved : CoefficientTarget := by
  intro m a b hd hm ha hb hlarge
  let K := admissibleSet m a b
  have hpos (x : ScalarTriple m) (hx : x ∈ K) : 0 < rankTwoMax x.1 :=
    rankTwoMax_pos (admissible_exists_rank_two hx ha hb hd hm hlarge)
  by_cases hK : K.Nonempty
  · have hcont : Continuous (fun x : ScalarTriple m => rankTwoMax x.1) :=
      (rankTwoMax_continuous m).comp continuous_fst
    obtain ⟨x, hx, hmin⟩ := (admissibleSet_compact m a b).exists_isMinOn hK hcont.continuousOn
    refine ⟨rankTwoMax x.1, hpos x hx, ?_⟩
    intro Ψ f g h
    have hmem : (Ψ, f, g) ∈ K := h
    obtain ⟨P, hr, he⟩ := rankTwoMax_attained (hpos _ hmem)
    refine ⟨P, hr, ?_⟩
    rw [← he]
    exact hmin hmem
  · refine ⟨1, by norm_num, ?_⟩
    intro Ψ f g h
    exact (hK ⟨(Ψ,f,g), h⟩).elim

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.coefficientTarget_proved := @_root_.OAI.Cotype.coefficientTarget_proved
