-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:50:24.373974+00:00
-- url     : https://prove2.me/submissions/b8698e79-4c50-4b36-8ecd-45b3c1ff4df2

import Mathlib
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S064

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Scalar kernels of the actual multicolor matrix

The tensor coordinates below describe entries of the existing swap/projector
operator. They do not introduce a new matrix chosen only for its rank or support.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

theorem eq_iff_pair_spectators (i : Fin Δ) (u y : UniversalType r Q Δ) :
    u = y ↔ SpectatorsAgree i u y ∧ ∀ l, pair i u l = pair i y l := by
  constructor
  · rintro rfl
    exact ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  · rintro ⟨hs, hp⟩
    apply UniversalType.ext
    · funext l
      exact congrArg Prod.fst (hp l)
    · funext j l
      by_cases hj : j = i
      · subst j
        exact congrArg Prod.snd (hp l)
      · exact hs j hj l

section Field

variable {K : Type*} [Field K]

theorem delta_eq_product (i : Fin Δ) (u y : UniversalType r Q Δ) :
    MatrixSupport.delta y u =
      background (K := K) i u y * ∏ l, plain i u y l := by
  classical
  by_cases h : u = y
  · subst y
    simp [MatrixSupport.delta, background, SpectatorsAgree, plain]
  · by_cases hs : SpectatorsAgree i u y
    · have hp : ¬ ∀ l, pair i u l = pair i y l :=
        fun hp => h ((eq_iff_pair_spectators i u y).mpr ⟨hs, hp⟩)
      simp [MatrixSupport.delta, h, background, hs, plain, Fintype.prod_boole, hp]
    · simp [MatrixSupport.delta, h, background, hs]

theorem partialKernel_empty (i : Fin Δ) (u y : UniversalType r Q Δ) :
    partialKernel (K := K) i ∅ u y = MatrixSupport.delta y u := by
  simp only [partialKernel, factor, Finset.notMem_empty, ↓reduceIte]
  exact (delta_eq_product i u y).symm

theorem partialKernel_insert (i : Fin Δ) (s : Finset (Fin Q))
    (a : Fin Q) (ha : a ∉ s) (u y : UniversalType r Q Δ) :
    partialKernel (K := K) i (insert a s) u y =
      partialKernel i s u y -
        partialKernel i s (MatrixSupport.swapPositions i {a} u) y := by
  classical
  let rest := ∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a, factor (K := K) i s u y l
  have hrest :
      (∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a, factor (K := K) i (insert a s) u y l) =
        rest := by
    apply Finset.prod_congr rfl
    intro l hl
    have hla : l ≠ a := (Finset.mem_erase.mp hl).1
    simp [factor, hla]
  have hswap :
      (∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a,
        factor (K := K) i s (MatrixSupport.swapPositions i {a} u) y l) = rest := by
    apply Finset.prod_congr rfl
    intro l hl
    have hla : l ≠ a := (Finset.mem_erase.mp hl).1
    simp [factor, hla]
  have hprod (f : Fin Q → K) :
      (∏ l, f l) = f a * ∏ l ∈ (Finset.univ : Finset (Fin Q)).erase a, f l :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)).symm
  unfold partialKernel
  rw [background_swap, hprod, hprod, hprod, hrest, hswap]
  simp only [factor, Finset.mem_insert_self, ite_true, if_true, ha, ite_false,
    plain_swap, Finset.mem_singleton_self, ite_true]
  dsimp only [rest, factor]
  ring

/-- Each actual difference operator affects exactly its own coordinate pair. -/
theorem differenceProduct_eq_partialKernel (i : Fin Δ) (as : List (Fin Q))
    (ha : as.Nodup) (u y : UniversalType r Q Δ) :
    MatrixSupport.differenceProduct i as (MatrixSupport.delta y) u =
      partialKernel (K := K) i as.toFinset u y := by
  induction as generalizing u with
  | nil => exact (partialKernel_empty i u y).symm
  | cons a as ih =>
      have hn := List.nodup_cons.mp ha
      rw [MatrixSupport.differenceProduct, ih hn.2, ih hn.2, List.toFinset_cons]
      exact (partialKernel_insert i as.toFinset a (by simpa using hn.1) u y).symm

end Field

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScalarBinomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shifted signed binomial coefficients

Multiplication by `(-X)^A` shifts the binomial coefficients by `A` and
multiplies them by the constant sign `(-1)^A`. The weighted-prefix identity
accounts for the vanishing coefficients below that shift.
-/

namespace SubexponentialSAT.Subexp.ScalarBinomial

open Polynomial
open scoped BigOperators

variable {K : Type*} [CommRing K]

theorem coeff_signed_binomial (A B j : ℕ) :
    (((-X : K[X]) ^ A) * (1 + X) ^ B).coeff j =
      if A ≤ j then (-1 : K) ^ A * (B.choose (j - A) : K) else 0 := by
  have hX : (-X : K[X]) = C (-1 : K) * X := by simp
  rw [hX, mul_pow, ← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [coeff_one_add_X_pow]
  by_cases hj : A ≤ j <;> simp [hj]

theorem weighted_prefix (a : ℕ → K) (A B R : ℕ) :
    (∑ j ∈ Finset.range R, a j * (((-X : K[X]) ^ A) * (1 + X) ^ B).coeff j) =
      (-1 : K) ^ A *
        ∑ k ∈ Finset.range (R - A), a (A + k) * (B.choose k : K) := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih, coeff_signed_binomial]
      by_cases h : A ≤ R
      · rw [ite_eq_left h, Nat.succ_sub h, Finset.sum_range_succ, mul_add,
          Nat.add_sub_of_le h]
        rw [mul_left_comm (a R) ((-1 : K) ^ A)]
      · have hlt : R < A := lt_of_not_ge h
        have hnext : R + 1 ≤ A := Nat.succ_le_of_lt hlt
        simp [h, Nat.sub_eq_zero_of_le hlt.le, Nat.sub_eq_zero_of_le hnext]

end SubexponentialSAT.Subexp.ScalarBinomial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A scalar generating polynomial for the actual matrix entries

The coefficient of degree j equals 2^j times the j-th elementary projector
kernel. Consequently normalized coefficients need only scalar polynomial
arithmetic, with no enumeration of subsets in the eventual implementation.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem prod_choice {ι : Type*} [DecidableEq ι] (s A : Finset ι) (hA : A ⊆ s)
    (p q : ι → K) :
    (∏ l ∈ s, if l ∈ A then q l else p l) =
      (∏ l ∈ A, q l) * ∏ l ∈ s \ A, p l := by
  rw [Finset.prod_ite]
  have hf : s.filter (fun l => l ∈ A) = A := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => hA h)
  have hg : s.filter (fun l => l ∉ A) = s \ A := by
    ext l
    simp
  rw [hf, hg]

theorem linear_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p q : ι → K) :
    (∏ l ∈ s, (C (p l) + C (q l) * X)) =
      ∑ A ∈ s.powerset,
        C ((∏ l ∈ A, q l) * ∏ l ∈ s \ A, p l) * X ^ A.card := by
  rw [show (∏ l ∈ s, (C (p l) + C (q l) * X)) =
      ∏ l ∈ s, (C (q l) * X + C (p l)) by
    apply Finset.prod_congr rfl
    intro l hl
    ring]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, ← map_prod, map_mul]
  ring

theorem coeff_linear_product {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p q : ι → K) (j : ℕ) :
    (∏ l ∈ s, (C (p l) + C (q l) * X)).coeff j =
      ∑ A ∈ s.powersetCard j,
        (∏ l ∈ A, q l) * ∏ l ∈ s \ A, p l := by
  rw [linear_product_expansion, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp [Finset.powersetCard_eq_filter, eq_comm]

theorem partialKernel_fullSwap (i : Fin Δ) (t : Fin Q)
    (A : Finset (Fin Q)) (hA : A ⊆ MatrixSupport.activePositions t)
    (u y : UniversalType r Q Δ) :
    partialKernel (K := K) i A
        (MatrixSupport.swapPositions i (MatrixSupport.activePositions t) u) y =
      (background i u y * plain i u y t) *
        ((∏ l ∈ A, (flipped i u y l - plain i u y l)) *
          ∏ l ∈ MatrixSupport.activePositions t \ A, flipped i u y l) := by
  classical
  have ht : t ∉ A := by
    intro ht
    simpa [MatrixSupport.activePositions] using hA ht
  have split (f : Fin Q → K) :
      (∏ l, f l) = f t * ∏ l ∈ MatrixSupport.activePositions t, f l :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ t)).symm
  rw [partialKernel, background_swap, split]
  have he : factor (K := K) i A
      (MatrixSupport.swapPositions i (MatrixSupport.activePositions t) u) y t =
        plain i u y t := by
    simp [factor, ht, MatrixSupport.activePositions]
  rw [he, ← mul_assoc]
  congr 1
  calc
    _ = ∏ l ∈ MatrixSupport.activePositions t,
          if l ∈ A then flipped i u y l - plain i u y l else flipped i u y l := by
      apply Finset.prod_congr rfl
      intro l hl
      simp only [factor, plain_swap, flipped_swap, hl, ite_true, if_true]
    _ = _ := prod_choice (MatrixSupport.activePositions t) A hA _ _

/-- The factor 2^j is precisely canceled by using normalized coefficients. -/
theorem coeff_kernelPolynomial (h2 : (2 : K) ≠ 0) (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (j : ℕ) :
    (kernelPolynomial (K := K) i t u y).coeff j =
      (2 : K) ^ j * MatrixSupport.elementaryProjector i t j
        (MatrixSupport.delta y) (MatrixSupport.swapPositions i (MatrixSupport.activePositions t) u) := by
  classical
  rw [kernelPolynomial, coeff_C_mul, coeff_linear_product,
    MatrixSupport.elementaryProjector, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hs := (Finset.mem_powersetCard.mp hA).1
  have hc := (Finset.mem_powersetCard.mp hA).2
  rw [MatrixSupport.projectorProduct, Finset.length_toList, hc,
    ← mul_assoc ((2 : K) ^ j) ((2 : K)⁻¹ ^ j) _]
  have hcancel : (2 : K) ^ j * (2 : K)⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ h2, one_pow]
  rw [hcancel, one_mul, differenceProduct_eq_partialKernel i A.toList A.nodup_toList,
    Finset.toList_toFinset, partialKernel_fullSwap i t A hs]

/-- This is equality with the existing operator's entry, not an assumed
specification for a replacement matrix. -/
theorem matrixEntry_eq_weighted_coeff (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (R : ℕ) (a : ℕ → K) (u y : UniversalType r Q Δ) :
    MatrixSupport.matrixEntry i t R (fun j => a j * (2 : K) ^ j) u y =
      ∑ j ∈ Finset.range R, a j * (kernelPolynomial i t u y).coeff j := by
  unfold MatrixSupport.matrixEntry
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_kernelPolynomial h2]
  ring

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-! The scalar kernel has only three nonzero local factors: 1, -X, and 1+X. -/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem unchanged_subset (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    unchanged i t u y ⊆ MatrixSupport.activePositions t := Finset.filter_subset _ _

theorem transposed_subset (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    transposed i t u y ⊆ MatrixSupport.activePositions t := Finset.filter_subset _ _

theorem local_factor_of_compatible (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (hc : Compatible i t u y)
    (l : Fin Q) (hl : l ∈ MatrixSupport.activePositions t) :
    (C (flipped (K := K) i u y l) + C (flipped i u y l - plain i u y l) * X) =
      (if l ∈ unchanged i t u y then -X else 1) *
        (if l ∈ transposed i t u y then 1 + X else 1) := by
  have hlt : l ≠ t := (Finset.mem_erase.mp hl).1
  have hp := hc.2.2 l hlt
  by_cases hf : u.head l = u.slot i l
  · have he : (u.slot i l, u.head l) = pair i u l := by simp [pair, hf]
    have hs : pair i u l = pair i y l := hp.elim id (fun h => he.symm.trans h)
    have ht : (u.slot i l, u.head l) = pair i y l := he.trans hs
    simp only [plain, flipped, hs, ht, ite_true, if_true, sub_self,
      map_one, map_zero, zero_mul, add_zero]
    simp [unchanged, transposed, hf]
  · by_cases hs : pair i u l = pair i y l
    · have ht : (u.slot i l, u.head l) ≠ pair i y l := by
        intro ht
        exact hf (congrArg Prod.fst (hs.trans ht.symm))
      simp [plain, flipped, hs, ht, unchanged, transposed, hf, hl]
    · have ht : (u.slot i l, u.head l) = pair i y l := hp.resolve_left hs
      simp [plain, flipped, hs, ht, unchanged, transposed, hf, hl]

theorem prod_indicator {ι : Type*} [DecidableEq ι] (s A : Finset ι) (hA : A ⊆ s)
    (z : K[X]) : (∏ l ∈ s, if l ∈ A then z else 1) = z ^ A.card := by
  rw [Finset.prod_ite]
  have hf : s.filter (fun l => l ∈ A) = A := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => hA h)
  rw [hf]
  simp

theorem kernelPolynomial_of_compatible (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (hc : Compatible i t u y) :
    kernelPolynomial (K := K) i t u y =
      (-X) ^ (unchanged i t u y).card * (1 + X) ^ (transposed i t u y).card := by
  classical
  have hb : background (K := K) i u y * plain i u y t = 1 := by
    simp [background, plain, hc.1, hc.2.1]
  rw [kernelPolynomial, hb, map_one, one_mul]
  have hprod :
      (∏ l ∈ MatrixSupport.activePositions t,
        (C (flipped (K := K) i u y l) + C (flipped i u y l - plain i u y l) * X)) =
      ∏ l ∈ MatrixSupport.activePositions t,
        (if l ∈ unchanged i t u y then -X else 1) *
          (if l ∈ transposed i t u y then 1 + X else 1) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact local_factor_of_compatible i t u y hc l hl
  rw [hprod, Finset.prod_mul_distrib,
    prod_indicator _ _ (unchanged_subset i t u y),
    prod_indicator _ _ (transposed_subset i t u y)]

theorem kernelPolynomial_of_incompatible (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (hc : ¬ Compatible i t u y) :
    kernelPolynomial (K := K) i t u y = 0 := by
  classical
  by_cases hs : SpectatorsAgree i u y
  · by_cases ht : pair i u t = pair i y t
    · have hbad : ¬ ∀ l, l ≠ t →
          pair i u l = pair i y l ∨ (u.slot i l, u.head l) = pair i y l :=
        fun h => hc ⟨hs, ht, h⟩
      push Not at hbad
      obtain ⟨l, hlt, hsame, hswap⟩ := hbad
      have hl : l ∈ MatrixSupport.activePositions t := by
        simp [MatrixSupport.activePositions, hlt]
      have hz :
          (C (flipped (K := K) i u y l) + C (flipped i u y l - plain i u y l) * X) = 0 := by
        simp [plain, flipped, hsame, hswap]
      rw [kernelPolynomial, Finset.prod_eq_zero hl hz, mul_zero]
    · simp [kernelPolynomial, plain, ht]
  · simp [kernelPolynomial, background, hs]

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-!
# Exact binomial formula for the implemented multicolor matrix

This connects scalar additions and sign changes to the very same matrix
used in the support and rank proofs. The only normalization hypothesis is
that the field has characteristic different from two.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

/-- Exact scalar entry, including incompatible rows and columns and the
case where the mandatory number of differences exceeds the cutoff R. -/
theorem matrixEntry_normalized (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (R : ℕ) (a : ℕ → K) (u y : UniversalType r Q Δ) :
    MatrixSupport.matrixEntry i t R (fun j => a j * (2 : K) ^ j) u y =
      if Compatible i t u y then
        (-1 : K) ^ (unchanged i t u y).card *
          ∑ k ∈ Finset.range (R - (unchanged i t u y).card),
            a ((unchanged i t u y).card + k) * ((transposed i t u y).card.choose k : K)
      else 0 := by
  classical
  rw [matrixEntry_eq_weighted_coeff h2]
  by_cases hc : Compatible i t u y
  · rw [ite_eq_left hc]
    simp_rw [kernelPolynomial_of_compatible i t u y hc]
    exact ScalarBinomial.weighted_prefix a _ _ _
  · simp only [ite_eq_right hc, kernelPolynomial_of_incompatible i t u y hc,
      Polynomial.coeff_zero, mul_zero, Finset.sum_const_zero]

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable scalar formulas for the exact cleared integer matrix entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

theorem scalarEntry_cast_oai (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    (scalarEntry i t A R u y : ℚ) =
      (LayoutNumerator.denominator R : ℚ) * matrixEntry i t R
        (fun j => (coefficientAt A R j : ℚ)) u y := by
  let a : ℕ → ℚ := fun j => (coefficientAt A R j : ℚ) * (2 : ℚ)⁻¹ ^ j
  have ha : (fun j => a j * (2 : ℚ) ^ j) =
      fun j => (coefficientAt A R j : ℚ) := by
    funext j
    dsimp [a]
    rw [mul_assoc, ← mul_pow]
    norm_num
  have he := matrixEntry_normalized (K := ℚ) (by norm_num) i t R a u y
  rw [ha] at he
  rw [he]
  by_cases hc : Compatible i t u y
  · simp only [scalarEntry, ite_eq_left hc, scalarSum, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_sum, Int.cast_ofNat, Int.cast_natCast]
    rw [mul_left_comm (LayoutNumerator.denominator R : ℚ)]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hj : (unchanged i t u y).card + k < R := by
      have hk' := Finset.mem_range.mp hk
      omega
    have hp := LayoutNumerator.pow_two_clear ℚ (by norm_num) R
      ((unchanged i t u y).card + k) hj
    simp only [LayoutNumerator.denominator, Int.cast_pow, Int.cast_ofNat]
    dsimp [a]
    rw [hp]
    ring
  · simp [scalarEntry, hc]

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast_oai
