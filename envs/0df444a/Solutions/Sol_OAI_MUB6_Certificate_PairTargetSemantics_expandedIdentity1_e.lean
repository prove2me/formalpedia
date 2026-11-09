-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:17:50.613243+00:00
-- url     : https://prove2.me/submissions/a7f3ae71-a167-41fd-bdbd-88204c3c1e2d

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm11_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm12_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm13_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm14_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm16_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm17_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm18_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm19_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm21_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm22_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm23_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm24_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm26_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm6_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm7_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm8_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm9_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_split_embedding (e : A ↪ B) (f : B → V) :
    (∑ b, f b) = (∑ a, f (e a)) + ∑ b : {b // b ∉ Set.range e}, f b := by
  classical
  let E : A ⊕ {b // b ∉ Set.range e} ≃ B :=
    (e.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range e))
  have h := E.sum_comp f
  simpa [E, Fintype.sum_sum_type, Equiv.trans_apply, Equiv.sumCongr_apply] using h.symm

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

theorem sum_samples_split {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin p ↪ B, ∑ b, f e b) =
      (∑ e : Fin p ↪ B, ∑ j, f e (e j)) +
      ∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0) := by
  classical
  calc
    _ = ∑ e : Fin p ↪ B,
        ((∑ j, f e (e j)) + ∑ b : {b // b ∉ Set.range e}, f e b) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_split_embedding e (f e)
    _ = _ := by rw [Finset.sum_add_distrib, sum_injective_extension]

theorem sum_contraction {p : ℕ} (f : (Fin p ↪ B) → B → V)
    (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin p, ∑ e : Fin p ↪ B, f e (e j)) +
      (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) = 0 := by
  classical
  rw [Finset.sum_comm]
  rw [← sum_samples_split]
  simp [h]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

/-- The normalized counting identity used for an order-one contraction.
At most n rows are sampled; the saturated boundary case is separate. -/
theorem average_contraction {p n : ℕ} (hp : p < n)
    (f : (Fin p ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    ((n - p : ℕ) : ℝ) *
      average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e) (e 0)) +
      (∑ j : Fin p, average (fun e : Fin p ↪ Fin n => f e (e j))) = 0 := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  have hc : ((n - p : ℕ) : ℝ) * (Fintype.card (Fin (p + 1) ↪ Fin n) : ℝ)⁻¹ =
      (Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ := by
    rw [embedding_succ_card, Nat.cast_mul, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hs := sum_contraction f h
  simp only [average]
  rw [← mul_assoc, hc, ← Finset.mul_sum, ← mul_add]
  rw [add_comm] at hs
  rw [hs, mul_zero]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_two {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) :
    ∑ i, f i = f 0 + f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern2_0 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 = f 0)
    : ∀ i j, family2.label 0 i = family2.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem pattern2_1 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 ≠ f 0)
    : ∀ i j, family2.label 1 i = family2.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem covers2 {B : Type*} (f : Fin 2 → B) :
    ∃ p, ∀ i j, (family2.label p i = family2.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    refine ⟨0, ?_⟩
    apply pattern2_0 f; simp_all [eq_comm]
  ·
    refine ⟨1, ?_⟩
    apply pattern2_1 f; simp_all [eq_comm]

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

/-- A uniform injection of all six row indices is a uniform permutation.
This identifies the general partition theorem with the paper's pair average. -/
theorem averagedRowProducts_eq_pairAverage {n : ℕ} (H : CMatrix)
    (A : Matrix Coord (Fin n) ℤ) :
    averagedRowProducts H A =
      pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) := by
  let f : Equiv.Perm Coord → ℝ := fun π =>
    ((∏ j, g (fun i k => H (π i) k) (fun i => A i j)).re +
      (∏ j, g (fun i k => H k (π i)) (fun i => A i j)).re) / 2
  calc
    averagedRowProducts H A =
        average (f ∘ Equiv.embeddingEquivOfFinite Coord) := by rfl
    _ = average f := average_equiv (Equiv.embeddingEquivOfFinite Coord) f
    _ = _ := rfl

theorem pairAverage_products_partition {n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix Coord (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  rw [← averagedRowProducts_eq_pairAverage H A]
  exact averagedRowProducts_partition hH A F cover

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairTermSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6.Certificate.PairTargetSemantics

private theorem sumterms1_at0 : terms1 0 = term0 := rfl
private theorem sumterms1_at1 : terms1 1 = term1 := rfl
private theorem sumterms1_at2 : terms1 2 = term2 := rfl
private theorem sumterms1_at3 : terms1 3 = term3 := rfl
private theorem sumterms1_at4 : terms1 4 = term4 := rfl
private theorem sumterms1_at5 : terms1 5 = term5 := rfl
private theorem sumterms1_at6 : terms1 6 = term6 := rfl
private theorem sumterms1_at7 : terms1 7 = term7 := rfl
private theorem sumterms1_at8 : terms1 8 = term8 := rfl
private theorem sumterms1_at9 : terms1 9 = term9 := rfl
private theorem sumterms1_at10 : terms1 10 = term10 := rfl
private theorem sumterms1_at11 : terms1 11 = term11 := rfl
private theorem sumterms1_at12 : terms1 12 = term12 := rfl
private theorem sumterms1_at13 : terms1 13 = term13 := rfl
private theorem sumterms1_at14 : terms1 14 = term14 := rfl
private theorem sumterms1_at15 : terms1 15 = term15 := rfl
private theorem sumterms1_at16 : terms1 16 = term16 := rfl
private theorem sumterms1_at17 : terms1 17 = term17 := rfl
private theorem sumterms1_at18 : terms1 18 = term18 := rfl
private theorem sumterms1_at19 : terms1 19 = term19 := rfl
private theorem sumterms1_at20 : terms1 20 = term20 := rfl
private theorem sumterms1_at21 : terms1 21 = term21 := rfl
private theorem sumterms1_at22 : terms1 22 = term22 := rfl
private theorem sumterms1_at23 : terms1 23 = term23 := rfl
private theorem sumterms1_at24 : terms1 24 = term24 := rfl
private theorem sumterms1_at25 : terms1 25 = term26 := rfl
theorem sum_terms1_expand {R : Type*} [AddCommMonoid R] (F : Term → R) :
    (∑ i : Fin 26, F (terms1 i)) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term26 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms1 0) + (F (terms1 1) + (F (terms1 2) + (F (terms1 3) + (F (terms1 4) + (F (terms1 5) + (F (terms1 6) + (F (terms1 7) + (F (terms1 8) + (F (terms1 9) + (F (terms1 10) + (F (terms1 11) + (F (terms1 12) + (F (terms1 13) + (F (terms1 14) + (F (terms1 15) + (F (terms1 16) + (F (terms1 17) + (F (terms1 18) + (F (terms1 19) + (F (terms1 20) + (F (terms1 21) + (F (terms1 22) + (F (terms1 23) + (F (terms1 24) + (F (terms1 25) + 0)))))))))))))))))))))))))) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term26
  simp only [sumterms1_at0, sumterms1_at1, sumterms1_at2, sumterms1_at3, sumterms1_at4, sumterms1_at5, sumterms1_at6, sumterms1_at7, sumterms1_at8, sumterms1_at9, sumterms1_at10, sumterms1_at11, sumterms1_at12, sumterms1_at13, sumterms1_at14, sumterms1_at15, sumterms1_at16, sumterms1_at17, sumterms1_at18, sumterms1_at19, sumterms1_at20, sumterms1_at21, sumterms1_at22, sumterms1_at23, sumterms1_at24, sumterms1_at25, add_zero, add_assoc]

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4044 = injectiveMoment H node202 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5116 = injectiveMoment H node45 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5123 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5123 = injectiveMoment H raw5123step0 := by
      have hz : ∀ j, raw5123 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5123step0 = (fun i j => raw5123 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5123 permutation241 hz
    injectiveMoment H raw5123step0 = injectiveMoment H raw5123step1 := by
      have hz : ∀ j, raw5123step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5123step1 = (fun i j => raw5123step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5123step0 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5124 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5124 = injectiveMoment H raw5124step0 := by
      have hz : ∀ j, raw5124 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5124step0 = (fun i j => raw5124 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5124 permutation241 hz
    injectiveMoment H raw5124step0 = injectiveMoment H raw5124step1 := by
      have hz : ∀ j, raw5124step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5124step1 = (fun i j => raw5124step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5124step0 permutation80 hz
    injectiveMoment H raw5124step1 = injectiveMoment H raw5124step2 := by
      have heq : raw5124step2 = (fun i j => raw5124step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5124step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

theorem canonical5127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5127 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5127 = injectiveMoment H raw5127step0 := by
      have hz : ∀ j, raw5127 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw5127step0 = (fun i j => raw5127 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5127 permutation221 hz
    _ = injectiveMoment H node232 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5164 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5164 = injectiveMoment H raw5164step0 := by
      have hz : ∀ j, raw5164 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5164step0 = (fun i j => raw5164 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164 permutation241 hz
    injectiveMoment H raw5164step0 = injectiveMoment H raw5164step1 := by
      have hz : ∀ j, raw5164step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5164step1 = (fun i j => raw5164step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164step0 permutation80 hz
    injectiveMoment H raw5164step1 = injectiveMoment H raw5164step2 := by
      have hz : ∀ j, raw5164step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5164step2 = (fun i j => raw5164step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5848 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5848 = injectiveMoment H raw5848step0 := by
      have heq : raw5848step0 = raw5848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5848).symm
    injectiveMoment H raw5848step0 = injectiveMoment H raw5848step1 := by
      have heq : raw5848step1 = (fun i j => raw5848step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5848step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5857 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw5857 = injectiveMoment H raw5857step0 := by
      have heq : raw5857step0 = -raw5857 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5857).symm
    injectiveMoment H raw5857step0 = injectiveMoment H raw5857step1 := by
      have heq : raw5857step1 = (fun i j => raw5857step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5857step0 permutation32 permutation3
    _ = injectiveMoment H node167 := by rfl

theorem canonical5864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5864 = injectiveMoment H node258 := by
  rfl

theorem canonical5865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5865 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw5865 = injectiveMoment H raw5865step0 := by
      have heq : raw5865step0 = (fun i j => raw5865 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5865 permutation10 permutation3
    _ = injectiveMoment H node258 := by rfl

theorem canonical5872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5872 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw5872 = injectiveMoment H raw5872step0 := by
      have heq : raw5872step0 = (fun i j => raw5872 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5872 permutation9 permutation5
    _ = injectiveMoment H node175 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5937 = injectiveMoment H node268 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5972 = injectiveMoment H node56 := by
  rfl

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6735 = injectiveMoment H node275 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7625 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7625 = injectiveMoment H raw7625step0 := by
      have hz : ∀ j, raw7625 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw7625step0 = (fun i j => raw7625 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7625 permutation221 hz
    injectiveMoment H raw7625step0 = injectiveMoment H raw7625step1 := by
      have heq : raw7625step1 = (fun i j => raw7625step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7625step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7668 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7668 = injectiveMoment H raw7668step0 := by
      have hz : ∀ j, raw7668 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7668step0 = (fun i j => raw7668 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668 permutation241 hz
    injectiveMoment H raw7668step0 = injectiveMoment H raw7668step1 := by
      have hz : ∀ j, raw7668step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7668step1 = (fun i j => raw7668step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668step0 permutation80 hz
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7982 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7982 = injectiveMoment H raw7982step0 := by
      have hz : ∀ j, raw7982 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7982step0 = (fun i j => raw7982 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982 permutation308 hz
    injectiveMoment H raw7982step0 = injectiveMoment H raw7982step1 := by
      have hz : ∀ j, raw7982step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7982step1 = (fun i j => raw7982step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step0 permutation128 hz
    injectiveMoment H raw7982step1 = injectiveMoment H raw7982step2 := by
      have hz : ∀ j, raw7982step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7982step2 = (fun i j => raw7982step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step1 permutation27 hz
    injectiveMoment H raw7982step2 = injectiveMoment H raw7982step3 := by
      have hz : ∀ j, raw7982step2 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7982step3 = (fun i j => raw7982step2 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step2 permutation7 hz
    injectiveMoment H raw7982step3 = injectiveMoment H raw7982step4 := by
      have hz : ∀ j, raw7982step3 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7982step4 = (fun i j => raw7982step3 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step3 permutation2 hz
    injectiveMoment H raw7982step4 = injectiveMoment H raw7982step5 := by
      have hz : ∀ j, raw7982step4 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7982step5 = (fun i j => raw7982step4 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step4 permutation0 hz
    injectiveMoment H raw7982step5 = injectiveMoment H raw7982step6 := by
      have hz : ∀ i, raw7982step5 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7982step6 = (fun i j => raw7982step5 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7982step5 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8160 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8160 = injectiveMoment H raw8160step0 := by
      have heq : raw8160step0 = (fun i j => raw8160 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8160 permutation15 permutation3
    _ = injectiveMoment H node279 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw845 = injectiveMoment H node117 := by
  calc
    injectiveMoment H raw845 = injectiveMoment H raw845step0 := by
      have hz : ∀ j, raw845 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw845step0 = (fun i j => raw845 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw845 permutation221 hz
    _ = injectiveMoment H node117 := by rfl

theorem canonical852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw852 = injectiveMoment H node23 := by
  rfl

theorem canonical853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw853 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw853 = injectiveMoment H raw853step0 := by
      have heq : raw853step0 = (fun i j => raw853 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw853 permutation10 permutation1
    _ = injectiveMoment H node23 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1332 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw1332 = injectiveMoment H raw1332step0 := by
      have heq : raw1332step0 = raw1332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1332).symm
    _ = injectiveMoment H node45 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2726 = injectiveMoment H node167 := by
  rfl

theorem canonical2727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2727 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw2727 = injectiveMoment H raw2727step0 := by
      have heq : raw2727step0 = (fun i j => raw2727 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2727 permutation10 permutation3
    _ = injectiveMoment H node167 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2767 = injectiveMoment H node175 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound23 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node23 = Sparse.eval value23 (momentVector H) := by
  have hc : momentVector H 68 = injectiveMoment H node23 := rfl
  simp [value23, Sparse.eval, hc]

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node45 = Sparse.eval value45 (momentVector H) := by
  have hc : momentVector H 27 = injectiveMoment H node45 := rfl
  simp [value45, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node117 = Sparse.eval value117 (momentVector H) := by
  have heq : pivotMatrix117 = (fun u v => node117 (pivotPermutation117 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node117 = injectiveMoment H pivotMatrix117 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix117 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix117 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix117 (0 : Fin 4)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (0 : Fin 4) = raw5116 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5116 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix117 (1 : Fin 4)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (1 : Fin 4) = raw872 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical872 hH).trans (sound25 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix117 (2 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (2 : Fin 4) = raw853 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical853 hH).trans (sound23 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix117 (3 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (3 : Fin 4) = raw852 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical852 hH).trans (sound23 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node117 + (injectiveMoment H (mergeFirst pivotMatrix117 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value117, value23, value25, value45, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node167 = Sparse.eval value167 (momentVector H) := by
  have hc : momentVector H 126 = injectiveMoment H node167 := rfl
  simp [value167, Sparse.eval, hc]

theorem sound175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node175 = Sparse.eval value175 (momentVector H) := by
  have heq : pivotMatrix175 = (fun u v => node175 (pivotPermutation175 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node175 = injectiveMoment H pivotMatrix175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix175 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix175 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (2 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node175 + (injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value175, value35, value56, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node202 = Sparse.eval value202 (momentVector H) := by
  have hc : momentVector H 24 = injectiveMoment H node202 := rfl
  simp [value202, Sparse.eval, hc]

theorem sound232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node232 = Sparse.eval value232 (momentVector H) := by
  have heq : pivotMatrix232 = (fun u v => node232 (pivotPermutation232 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node232 = injectiveMoment H pivotMatrix232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix232 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix232 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (1 : Fin 4) = raw5177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5177 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (2 : Fin 4) = raw5197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5197 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (3 : Fin 4) = raw5204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5204 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node232 + (injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value232, value11, value26, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node258 = Sparse.eval value258 (momentVector H) := by
  have hc : momentVector H 236 = injectiveMoment H node258 := rfl
  simp [value258, Sparse.eval, hc]

theorem sound268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node268 = Sparse.eval value268 (momentVector H) := by
  have heq : pivotMatrix268 = (fun u v => node268 (pivotPermutation268 u) v) := by apply Matrix.ext; unfold pivotMatrix268 node268 pivotPermutation268; decide +kernel
  have hmoment : injectiveMoment H node268 = injectiveMoment H pivotMatrix268 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix268 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix268 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix268 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (0 : Fin 3) = raw5547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5547; decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix268 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix268 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node268 + (injectiveMoment H (mergeFirst pivotMatrix268 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix268 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix268 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value268, value52, value56, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node275 = Sparse.eval value275 (momentVector H) := by
  have hc : momentVector H 30 = injectiveMoment H node275 := rfl
  simp [value275, Sparse.eval, hc]

theorem sound279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node279 = Sparse.eval value279 (momentVector H) := by
  have heq : pivotMatrix279 = (fun u v => node279.transpose (pivotPermutation279 u) v) := by apply Matrix.ext; unfold pivotMatrix279 node279 pivotPermutation279; decide +kernel
  have hmoment : injectiveMoment H node279 = injectiveMoment H pivotMatrix279 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix279 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix279 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (0 : Fin 2) = raw1332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw1332; decide +kernel
    rw [heq]
    exact (canonical1332 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (1 : Fin 2) = raw5848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw5848; decide +kernel
    rw [heq]
    exact (canonical5848 hH).trans (sound46 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node279 + (injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value279, value45, value46, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound856 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node856 = Sparse.eval value856 (momentVector H) := by
  have heq : pivotMatrix856 = (fun u v => node856 (pivotPermutation856 u) v) := by apply Matrix.ext; unfold pivotMatrix856 node856 pivotPermutation856; decide +kernel
  have hmoment : injectiveMoment H node856 = injectiveMoment H pivotMatrix856 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix856 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix856 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix856 (0 : Fin 4)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (0 : Fin 4) = raw6735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw6735; decide +kernel
    rw [heq]
    exact (canonical6735 hH).trans (sound275 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix856 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (1 : Fin 4) = raw5872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5872; decide +kernel
    rw [heq]
    exact (canonical5872 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix856 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix856 (3 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (3 : Fin 4) = raw5864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5864; decide +kernel
    rw [heq]
    exact (canonical5864 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node856 + (injectiveMoment H (mergeFirst pivotMatrix856 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value856, value175, value258, value275, Sparse.eval] at hc ⊢
  linarith

theorem sound858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node858 = Sparse.eval value858 (momentVector H) := by
  have heq : pivotMatrix858 = (fun u v => node858 (pivotPermutation858 u) v) := by apply Matrix.ext; unfold pivotMatrix858 node858 pivotPermutation858; decide +kernel
  have hmoment : injectiveMoment H node858 = injectiveMoment H pivotMatrix858 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix858 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix858 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix858 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (0 : Fin 4) = raw8160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw8160; decide +kernel
    rw [heq]
    exact (canonical8160 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix858 (1 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (1 : Fin 4) = raw5937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5937; decide +kernel
    rw [heq]
    exact (canonical5937 hH).trans (sound268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix858 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix858 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (3 : Fin 4) = raw5857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5857; decide +kernel
    rw [heq]
    exact (canonical5857 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node858 + (injectiveMoment H (mergeFirst pivotMatrix858 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value858, value167, value258, value268, value279, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node545 = Sparse.eval value545 (momentVector H) := by
  have heq : pivotMatrix545 = (fun u v => node545 (pivotPermutation545 u) v) := by apply Matrix.ext; unfold pivotMatrix545 node545 pivotPermutation545; decide +kernel
  have hmoment : injectiveMoment H node545 = injectiveMoment H pivotMatrix545 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix545 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix545 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix545 (0 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (0 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix545 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (1 : Fin 4) = raw2767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2767; decide +kernel
    rw [heq]
    exact (canonical2767 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix545 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (2 : Fin 4) = raw2727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2727; decide +kernel
    rw [heq]
    exact (canonical2727 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix545 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (3 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node545 + (injectiveMoment H (mergeFirst pivotMatrix545 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value545, value167, value175, value202, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem integerMergeCheck25 : integerMerge25 =
    Integer.Sparse.merge integerTerm1 integerTerm2 := by decide +kernel

theorem integerMergeEval25 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge25 x =
      Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck25, Integer.Sparse.eval_merge]

theorem integerMergeCheck26 : integerMerge26 =
    Integer.Sparse.merge integerTerm0 integerMerge25 := by decide +kernel

theorem integerMergeEval26 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge26 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck26, Integer.Sparse.eval_merge]
  rw [integerMergeEval25]
  all_goals ring

theorem integerMergeCheck27 : integerMerge27 =
    Integer.Sparse.merge integerTerm4 integerTerm5 := by decide +kernel

theorem integerMergeEval27 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge27 x =
      Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck27, Integer.Sparse.eval_merge]

theorem integerMergeCheck28 : integerMerge28 =
    Integer.Sparse.merge integerTerm3 integerMerge27 := by decide +kernel

theorem integerMergeEval28 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge28 x =
      Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck28, Integer.Sparse.eval_merge]
  rw [integerMergeEval27]
  all_goals ring

theorem integerMergeCheck29 : integerMerge29 =
    Integer.Sparse.merge integerMerge26 integerMerge28 := by decide +kernel

theorem integerMergeEval29 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge29 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck29, Integer.Sparse.eval_merge]
  rw [integerMergeEval26, integerMergeEval28]
  all_goals ring

theorem integerMergeCheck30 : integerMerge30 =
    Integer.Sparse.merge integerTerm7 integerTerm8 := by decide +kernel

theorem integerMergeEval30 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge30 x =
      Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck30, Integer.Sparse.eval_merge]

theorem integerMergeCheck31 : integerMerge31 =
    Integer.Sparse.merge integerTerm6 integerMerge30 := by decide +kernel

theorem integerMergeEval31 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge31 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck31, Integer.Sparse.eval_merge]
  rw [integerMergeEval30]
  all_goals ring

theorem integerMergeCheck32 : integerMerge32 =
    Integer.Sparse.merge integerTerm9 integerTerm10 := by decide +kernel

theorem integerMergeEval32 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge32 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x := by
  rw [integerMergeCheck32, Integer.Sparse.eval_merge]

theorem integerMergeCheck33 : integerMerge33 =
    Integer.Sparse.merge integerTerm11 integerTerm12 := by decide +kernel

theorem integerMergeEval33 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge33 x =
      Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck33, Integer.Sparse.eval_merge]

theorem integerMergeCheck34 : integerMerge34 =
    Integer.Sparse.merge integerMerge32 integerMerge33 := by decide +kernel

theorem integerMergeEval34 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge34 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck34, Integer.Sparse.eval_merge]
  rw [integerMergeEval32, integerMergeEval33]
  all_goals ring

theorem integerMergeCheck35 : integerMerge35 =
    Integer.Sparse.merge integerMerge31 integerMerge34 := by decide +kernel

theorem integerMergeEval35 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge35 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck35, Integer.Sparse.eval_merge]
  rw [integerMergeEval31, integerMergeEval34]
  all_goals ring

theorem integerMergeCheck36 : integerMerge36 =
    Integer.Sparse.merge integerMerge29 integerMerge35 := by decide +kernel

theorem integerMergeEval36 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge36 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck36, Integer.Sparse.eval_merge]
  rw [integerMergeEval29, integerMergeEval35]
  all_goals ring

theorem integerMergeCheck37 : integerMerge37 =
    Integer.Sparse.merge integerTerm14 integerTerm15 := by decide +kernel

theorem integerMergeEval37 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge37 x =
      Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck37, Integer.Sparse.eval_merge]

theorem integerMergeCheck38 : integerMerge38 =
    Integer.Sparse.merge integerTerm13 integerMerge37 := by decide +kernel

theorem integerMergeEval38 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge38 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck38, Integer.Sparse.eval_merge]
  rw [integerMergeEval37]
  all_goals ring

theorem integerMergeCheck39 : integerMerge39 =
    Integer.Sparse.merge integerTerm17 integerTerm18 := by decide +kernel

theorem integerMergeEval39 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge39 x =
      Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck39, Integer.Sparse.eval_merge]

theorem integerMergeCheck40 : integerMerge40 =
    Integer.Sparse.merge integerTerm16 integerMerge39 := by decide +kernel

theorem integerMergeEval40 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge40 x =
      Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck40, Integer.Sparse.eval_merge]
  rw [integerMergeEval39]
  all_goals ring

theorem integerMergeCheck41 : integerMerge41 =
    Integer.Sparse.merge integerMerge38 integerMerge40 := by decide +kernel

theorem integerMergeEval41 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge41 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck41, Integer.Sparse.eval_merge]
  rw [integerMergeEval38, integerMergeEval40]
  all_goals ring

theorem integerMergeCheck42 : integerMerge42 =
    Integer.Sparse.merge integerTerm20 integerTerm21 := by decide +kernel

theorem integerMergeEval42 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge42 x =
      Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck42, Integer.Sparse.eval_merge]

theorem integerMergeCheck43 : integerMerge43 =
    Integer.Sparse.merge integerTerm19 integerMerge42 := by decide +kernel

theorem integerMergeEval43 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge43 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck43, Integer.Sparse.eval_merge]
  rw [integerMergeEval42]
  all_goals ring

theorem integerMergeCheck44 : integerMerge44 =
    Integer.Sparse.merge integerTerm22 integerTerm23 := by decide +kernel

theorem integerMergeEval44 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge44 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x := by
  rw [integerMergeCheck44, Integer.Sparse.eval_merge]

theorem integerMergeCheck45 : integerMerge45 =
    Integer.Sparse.merge integerTerm24 integerTerm26 := by decide +kernel

theorem integerMergeEval45 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge45 x =
      Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck45, Integer.Sparse.eval_merge]

theorem integerMergeCheck46 : integerMerge46 =
    Integer.Sparse.merge integerMerge44 integerMerge45 := by decide +kernel

theorem integerMergeEval46 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge46 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck46, Integer.Sparse.eval_merge]
  rw [integerMergeEval44, integerMergeEval45]
  all_goals ring

theorem integerMergeCheck47 : integerMerge47 =
    Integer.Sparse.merge integerMerge43 integerMerge46 := by decide +kernel

theorem integerMergeEval47 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge47 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck47, Integer.Sparse.eval_merge]
  rw [integerMergeEval43, integerMergeEval46]
  all_goals ring

theorem integerMergeCheck48 : integerMerge48 =
    Integer.Sparse.merge integerMerge41 integerMerge47 := by decide +kernel

theorem integerMergeEval48 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge48 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck48, Integer.Sparse.eval_merge]
  rw [integerMergeEval41, integerMergeEval47]
  all_goals ring

theorem integerMergeCheck49 : integerMerge49 =
    Integer.Sparse.merge integerMerge36 integerMerge48 := by decide +kernel

theorem integerMergeEval49 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge49 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x + Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck49, Integer.Sparse.eval_merge]
  rw [integerMergeEval36, integerMergeEval48]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical0 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw0 = injectiveMoment H node856 := by
  calc
    injectiveMoment H extraRaw0 = injectiveMoment H extraRaw0step0 := by
      have heq : extraRaw0step0 = -extraRaw0 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw0).symm
    injectiveMoment H extraRaw0step0 = injectiveMoment H extraRaw0step1 := by
      have hz : ∀ j, extraRaw0step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw0step1 = (fun u v => extraRaw0step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw0step0 extraPermutation62 hz
    injectiveMoment H extraRaw0step1 = injectiveMoment H extraRaw0step2 := by
      have heq : extraRaw0step2 = (fun u v => extraRaw0step1 (extraPermutation24 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw0step1 extraPermutation24 extraPermutation5
    _ = injectiveMoment H node856 := by rfl

theorem extraCanonical1 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw1 = injectiveMoment H node545 := by
  calc
    injectiveMoment H extraRaw1 = injectiveMoment H extraRaw1step0 := by
      have heq : extraRaw1step0 = -extraRaw1 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw1).symm
    injectiveMoment H extraRaw1step0 = injectiveMoment H extraRaw1step1 := by
      have hz : ∀ j, extraRaw1step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw1step1 = (fun u v => extraRaw1step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw1step0 extraPermutation62 hz
    injectiveMoment H extraRaw1step1 = injectiveMoment H extraRaw1step2 := by
      have heq : extraRaw1step2 = (fun u v => extraRaw1step1 (extraPermutation24 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw1step1 extraPermutation24 extraPermutation5
    _ = injectiveMoment H node545 := by rfl

theorem extraCanonical2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw2 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw2 = injectiveMoment H extraRaw2step0 := by
      have hz : ∀ j, extraRaw2 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw2step0 = (fun u v => extraRaw2 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw2 extraPermutation66 hz
    injectiveMoment H extraRaw2step0 = injectiveMoment H extraRaw2step1 := by
      have hz : ∀ j, extraRaw2step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw2step1 = (fun u v => extraRaw2step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw2step0 extraPermutation39 hz
    _ = injectiveMoment H node65 := by rfl

theorem extraCanonical3 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw3 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw3 = injectiveMoment H extraRaw3step0 := by
      have heq : extraRaw3step0 = -extraRaw3 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw3).symm
    injectiveMoment H extraRaw3step0 = injectiveMoment H extraRaw3step1 := by
      have hz : ∀ j, extraRaw3step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw3step1 = (fun u v => extraRaw3step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw3step0 extraPermutation62 hz
    injectiveMoment H extraRaw3step1 = injectiveMoment H extraRaw3step2 := by
      have heq : extraRaw3step2 = (fun u v => extraRaw3step1 (extraPermutation26 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw3step1 extraPermutation26 extraPermutation5
    _ = injectiveMoment H node858 := by rfl

theorem extraCanonical4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw4 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw4 = injectiveMoment H extraRaw4step0 := by
      have hz : ∀ j, extraRaw4 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw4step0 = (fun u v => extraRaw4 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw4 extraPermutation67 hz
    injectiveMoment H extraRaw4step0 = injectiveMoment H extraRaw4step1 := by
      have hz : ∀ j, extraRaw4step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw4step1 = (fun u v => extraRaw4step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw4step0 extraPermutation39 hz
    _ = injectiveMoment H node65 := by rfl

theorem extraCanonical5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw5 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw5 = injectiveMoment H extraRaw5step0 := by
      have heq : extraRaw5step0 = -extraRaw5 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw5).symm
    injectiveMoment H extraRaw5step0 = injectiveMoment H extraRaw5step1 := by
      have hz : ∀ j, extraRaw5step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw5step1 = (fun u v => extraRaw5step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw5step0 extraPermutation62 hz
    injectiveMoment H extraRaw5step1 = injectiveMoment H extraRaw5step2 := by
      have heq : extraRaw5step2 = (fun u v => extraRaw5step1 (extraPermutation28 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw5step1 extraPermutation28 extraPermutation5
    _ = injectiveMoment H node858 := by rfl

theorem extraCanonical6 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw6 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw6 = injectiveMoment H extraRaw6step0 := by
      have hz : ∀ j, extraRaw6 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw6step0 = (fun u v => extraRaw6 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw6 extraPermutation62 hz
    injectiveMoment H extraRaw6step0 = injectiveMoment H extraRaw6step1 := by
      have heq : extraRaw6step1 = (fun u v => extraRaw6step0 (extraPermutation24 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw6step0 extraPermutation24 extraPermutation1
    _ = injectiveMoment H node232 := by rfl

theorem extraCanonical7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw7 = injectiveMoment H node856 := by
  calc
    injectiveMoment H extraRaw7 = injectiveMoment H extraRaw7step0 := by
      have hz : ∀ j, extraRaw7 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw7step0 = (fun u v => extraRaw7 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw7 extraPermutation62 hz
    _ = injectiveMoment H node856 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw35 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw35 = injectiveMoment H extraRaw35step0 := by
      have hz : ∀ j, extraRaw35 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw35step0 = (fun u v => extraRaw35 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw35 extraPermutation62 hz
    injectiveMoment H extraRaw35step0 = injectiveMoment H extraRaw35step1 := by
      have heq : extraRaw35step1 = (fun u v => extraRaw35step0 (extraPermutation34 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw35step0 extraPermutation34 extraPermutation1
    _ = injectiveMoment H node232 := by rfl

theorem extraCanonical36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw36 = injectiveMoment H node545 := by
  calc
    injectiveMoment H extraRaw36 = injectiveMoment H extraRaw36step0 := by
      have hz : ∀ j, extraRaw36 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw36step0 = (fun u v => extraRaw36 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw36 extraPermutation62 hz
    _ = injectiveMoment H node545 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical63 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw63 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw63 = injectiveMoment H extraRaw63step0 := by
      have hz : ∀ j, extraRaw63 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw63step0 = (fun u v => extraRaw63 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw63 extraPermutation63 hz
    injectiveMoment H extraRaw63step0 = injectiveMoment H extraRaw63step1 := by
      have hz : ∀ j, extraRaw63step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw63step1 = (fun u v => extraRaw63step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw63step0 extraPermutation39 hz
    injectiveMoment H extraRaw63step1 = injectiveMoment H extraRaw63step2 := by
      have heq : extraRaw63step2 = (fun u v => extraRaw63step1 (extraPermutation19 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw63step1 extraPermutation19 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical64 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw64 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw64 = injectiveMoment H extraRaw64step0 := by
      have hz : ∀ j, extraRaw64 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw64step0 = (fun u v => extraRaw64 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw64 extraPermutation62 hz
    injectiveMoment H extraRaw64step0 = injectiveMoment H extraRaw64step1 := by
      have heq : extraRaw64step1 = (fun u v => extraRaw64step0 (extraPermutation26 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw64step0 extraPermutation26 extraPermutation2
    _ = injectiveMoment H node858 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical90 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw90 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw90 = injectiveMoment H extraRaw90step0 := by
      have hz : ∀ j, extraRaw90 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw90step0 = (fun u v => extraRaw90 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw90 extraPermutation63 hz
    injectiveMoment H extraRaw90step0 = injectiveMoment H extraRaw90step1 := by
      have hz : ∀ j, extraRaw90step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw90step1 = (fun u v => extraRaw90step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw90step0 extraPermutation39 hz
    injectiveMoment H extraRaw90step1 = injectiveMoment H extraRaw90step2 := by
      have heq : extraRaw90step2 = (fun u v => extraRaw90step1 (extraPermutation23 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw90step1 extraPermutation23 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

theorem extraCanonical91 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw91 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw91 = injectiveMoment H extraRaw91step0 := by
      have hz : ∀ j, extraRaw91 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw91step0 = (fun u v => extraRaw91 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw91 extraPermutation62 hz
    injectiveMoment H extraRaw91step0 = injectiveMoment H extraRaw91step1 := by
      have heq : extraRaw91step1 = (fun u v => extraRaw91step0 (extraPermutation28 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw91step0 extraPermutation28 extraPermutation2
    _ = injectiveMoment H node858 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_PartitionRules
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem partitionWeight2_0 :
    (Fintype.card (Fin (EqualityPatterns.family2.blocks 0) ↪ Coord) : ℝ) / 6 ^ 2 = (1/6 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 2 = (1/6 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight2_1 :
    (Fintype.card (Fin (EqualityPatterns.family2.blocks 1) ↪ Coord) : ℝ) / 6 ^ 2 = (5/6 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 2 = (5/6 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition2 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 2) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 6 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 0)) +
      (5 / 6 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 1)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family2 EqualityPatterns.covers2
  rw [MixedSemantics.sum_fin_two] at h
  simpa only [partitionWeight2_0, partitionWeight2_1] using h

theorem partitionWeight3_0 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 0) ↪ Coord) : ℝ) / 6 ^ 3 = (1/36 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 3 = (1/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_1 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 1) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_2 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 2) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_3 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 3) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_4 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 4) ↪ Coord) : ℝ) / 6 ^ 3 = (5/9 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/9 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition3 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 3) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family3 EqualityPatterns.covers3
  rw [MixedSemantics.sum_fin_five] at h
  simpa only [partitionWeight3_0, partitionWeight3_1, partitionWeight3_2, partitionWeight3_3, partitionWeight3_4] using h

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition0 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term0.charges u j)).re) =
      Sparse.eval monomialValue0 (momentVector H) := by
  let A : Matrix Coord (Fin 2) ℤ := term0.charges
  change pairAverage H (fun K => (∏ j : Fin 2, g K (fun u => A u j)).re) = _
  have hp := pair_partition2 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family2.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family2.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  rw [hm0, hm1] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family2, EqualityPatterns.blocks2, Nat.descFactorial, monomialValue0, value0, value117, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm0 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term0 =
      Integer.Sparse.eval integerTerm0 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition0 hH]
  norm_num [term0, integerTerm0, monomialValue0, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition1 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term1.charges u j)).re) =
      Sparse.eval monomialValue1 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term1.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5127 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5127 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = raw7668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7668 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw0 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical0 hH).trans (sound856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue1, value0, value117, value232, value65, value856, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm1 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term1 =
      Integer.Sparse.eval integerTerm1 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition1 hH]
  norm_num [term1, integerTerm1, monomialValue1, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition10 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term10.charges u j)).re) =
      Sparse.eval monomialValue10 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term10.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw35 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical35 hH).trans (sound232 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw5164 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5164 hH).trans (sound11 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value545 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw36 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical36 hH).trans (sound545 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue10, value0, value11, value117, value232, value545, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm10 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term10 =
      Integer.Sparse.eval integerTerm10 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition10 hH]
  norm_num [term10, integerTerm10, monomialValue10, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition15 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term15.charges u j)).re) =
      Sparse.eval monomialValue15 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term15.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw63 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical63 hH).trans (sound46 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = extraRaw2 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical2 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw64 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical64 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue15, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm15 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term15 =
      Integer.Sparse.eval integerTerm15 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition15 hH]
  norm_num [term15, integerTerm15, monomialValue15, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition2 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term2.charges u j)).re) =
      Sparse.eval monomialValue2 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term2.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw7625 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7625 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = raw5164 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5164 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value545 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw1 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical1 hH).trans (sound545 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue2, value0, value11, value117, value232, value545, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm2 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term2 =
      Integer.Sparse.eval integerTerm2 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition2 hH]
  norm_num [term2, integerTerm2, monomialValue2, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition20 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term20.charges u j)).re) =
      Sparse.eval monomialValue20 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term20.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw90 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical90 hH).trans (sound46 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = extraRaw4 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical4 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw91 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical91 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue20, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm20 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term20 =
      Integer.Sparse.eval integerTerm20 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition20 hH]
  norm_num [term20, integerTerm20, monomialValue20, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition3 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term3.charges u j)).re) =
      Sparse.eval monomialValue3 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term3.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5124 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5124 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw2 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical2 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw3 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical3 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue3, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm3 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term3 =
      Integer.Sparse.eval integerTerm3 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition3 hH]
  norm_num [term3, integerTerm3, monomialValue3, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition4 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term4.charges u j)).re) =
      Sparse.eval monomialValue4 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term4.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5123 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5123 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw4 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical4 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw5 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical5 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue4, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm4 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term4 =
      Integer.Sparse.eval integerTerm4 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition4 hH]
  norm_num [term4, integerTerm4, monomialValue4, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition5 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term5.charges u j)).re) =
      Sparse.eval monomialValue5 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term5.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw6 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical6 hH).trans (sound232 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw7668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7668 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw7 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical7 hH).trans (sound856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue5, value0, value117, value232, value65, value856, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm5 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term5 =
      Integer.Sparse.eval integerTerm5 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition5 hH]
  norm_num [term5, integerTerm5, monomialValue5, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem expandedIdentity1_e_oai {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * expanded1 H =
      Integer.Sparse.eval integerMerge49 (PairSemantics.momentVector H) := by
  rw [integerMergeEval49]
  unfold expanded1
  rw [sum_terms1_expand]
  simp only [mul_add]
  rw [weightedTerm0 hH, weightedTerm1 hH, weightedTerm2 hH, weightedTerm3 hH, weightedTerm4 hH, weightedTerm5 hH, weightedTerm6_e hH, weightedTerm7_e hH, weightedTerm8_e hH, weightedTerm9_e hH, weightedTerm10 hH, weightedTerm11_e hH, weightedTerm12_e hH, weightedTerm13_e hH, weightedTerm14_e hH, weightedTerm15 hH, weightedTerm16_e hH, weightedTerm17_e hH, weightedTerm18_e hH, weightedTerm19_e hH, weightedTerm20 hH, weightedTerm21_e hH, weightedTerm22_e hH, weightedTerm23_e hH, weightedTerm24_e hH, weightedTerm26_e hH]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e_oai := @OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e_oai
