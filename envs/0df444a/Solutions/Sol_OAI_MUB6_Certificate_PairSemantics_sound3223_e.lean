-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3223_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T07:40:09.241204+00:00
-- url     : https://prove2.me/submissions/b5ddadbc-d619-4979-934f-d9b6be7c7ec8

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical51 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw51 = injectiveMoment H node7 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw340 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw340 = injectiveMoment H raw340step0 := by
      have heq : raw340step0 = raw340.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw340).symm
    _ = injectiveMoment H node84 := by rfl

theorem canonical346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw346 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw346 = injectiveMoment H raw346step0 := by
      have heq : raw346step0 = raw346.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw346).symm
    injectiveMoment H raw346step0 = injectiveMoment H raw346step1 := by
      have heq : raw346step1 = -raw346step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw346step0).symm
    injectiveMoment H raw346step1 = injectiveMoment H raw346step2 := by
      have heq : raw346step2 = (fun i j => raw346step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw346step1 permutation19 permutation5
    _ = injectiveMoment H node198 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3349 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw3349 = injectiveMoment H raw3349step0 := by
      have heq : raw3349step0 = raw3349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3349).symm
    _ = injectiveMoment H node197 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw357 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw357 = injectiveMoment H raw357step0 := by
      have heq : raw357step0 = raw357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw357).symm
    injectiveMoment H raw357step0 = injectiveMoment H raw357step1 := by
      have heq : raw357step1 = (fun i j => raw357step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw357step0 permutation10 permutation3
    _ = injectiveMoment H node84 := by rfl

theorem canonical362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw362 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw362 = injectiveMoment H raw362step0 := by
      have heq : raw362step0 = raw362.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw362).symm
    injectiveMoment H raw362step0 = injectiveMoment H raw362step1 := by
      have heq : raw362step1 = -raw362step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw362step0).symm
    injectiveMoment H raw362step1 = injectiveMoment H raw362step2 := by
      have heq : raw362step2 = (fun i j => raw362step1 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw362step1 permutation17 permutation5
    _ = injectiveMoment H node198 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3645 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw3645 = injectiveMoment H raw3645step0 := by
      have heq : raw3645step0 = raw3645.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3645).symm
    _ = injectiveMoment H node152 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3651 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw3651 = injectiveMoment H raw3651step0 := by
      have heq : raw3651step0 = raw3651.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3651).symm
    _ = injectiveMoment H node184 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3847 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3847 = injectiveMoment H raw3847step0 := by
      have heq : raw3847step0 = raw3847.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3847).symm
    injectiveMoment H raw3847step0 = injectiveMoment H raw3847step1 := by
      have heq : raw3847step1 = -raw3847step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3847step0).symm
    injectiveMoment H raw3847step1 = injectiveMoment H raw3847step2 := by
      have heq : raw3847step2 = (fun i j => raw3847step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3847step1 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4015 = injectiveMoment H node28 := by
  calc
    injectiveMoment H raw4015 = injectiveMoment H raw4015step0 := by
      have heq : raw4015step0 = -raw4015 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4015).symm
    injectiveMoment H raw4015step0 = injectiveMoment H raw4015step1 := by
      have heq : raw4015step1 = (fun i j => raw4015step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4015step0 permutation8 permutation3
    _ = injectiveMoment H node28 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4157 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4157 = injectiveMoment H raw4157step0 := by
      have heq : raw4157step0 = raw4157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4157).symm
    injectiveMoment H raw4157step0 = injectiveMoment H raw4157step1 := by
      have heq : raw4157step1 = -raw4157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4157step0).symm
    injectiveMoment H raw4157step1 = injectiveMoment H raw4157step2 := by
      have heq : raw4157step2 = (fun i j => raw4157step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4157step1 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4167 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw4167 = injectiveMoment H raw4167step0 := by
      have heq : raw4167step0 = raw4167.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4167).symm
    injectiveMoment H raw4167step0 = injectiveMoment H raw4167step1 := by
      have heq : raw4167step1 = (fun i j => raw4167step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4167step0 permutation13 permutation3
    _ = injectiveMoment H node140 := by rfl

theorem canonical4172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4172 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4172 = injectiveMoment H raw4172step0 := by
      have heq : raw4172step0 = raw4172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4172).symm
    injectiveMoment H raw4172step0 = injectiveMoment H raw4172step1 := by
      have heq : raw4172step1 = (fun i j => raw4172step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4172step0 permutation13 permutation3
    _ = injectiveMoment H node169 := by rfl

theorem canonical4173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4173 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw4173 = injectiveMoment H raw4173step0 := by
      have heq : raw4173step0 = raw4173.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4173).symm
    injectiveMoment H raw4173step0 = injectiveMoment H raw4173step1 := by
      have heq : raw4173step1 = (fun i j => raw4173step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4173step0 permutation13 permutation3
    _ = injectiveMoment H node162 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4197 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4197 = injectiveMoment H raw4197step0 := by
      have heq : raw4197step0 = raw4197.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4197).symm
    injectiveMoment H raw4197step0 = injectiveMoment H raw4197step1 := by
      have heq : raw4197step1 = (fun i j => raw4197step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4197step0 permutation13 permutation3
    _ = injectiveMoment H node197 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4256 = injectiveMoment H node2153 := by
  rfl

theorem canonical4257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4257 = injectiveMoment H node2154 := by
  rfl

theorem canonical4258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4258 = injectiveMoment H node2155 := by
  rfl

theorem canonical4260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4260 = injectiveMoment H node913 := by
  calc
    injectiveMoment H raw4260 = injectiveMoment H raw4260step0 := by
      have heq : raw4260step0 = raw4260.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4260).symm
    injectiveMoment H raw4260step0 = injectiveMoment H raw4260step1 := by
      have heq : raw4260step1 = (fun i j => raw4260step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4260step0 permutation27 permutation18
    _ = injectiveMoment H node913 := by rfl

theorem canonical4262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4262 = injectiveMoment H node770 := by
  calc
    injectiveMoment H raw4262 = injectiveMoment H raw4262step0 := by
      have heq : raw4262step0 = raw4262.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4262).symm
    injectiveMoment H raw4262step0 = injectiveMoment H raw4262step1 := by
      have heq : raw4262step1 = (fun i j => raw4262step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4262step0 permutation27 permutation18
    _ = injectiveMoment H node770 := by rfl

theorem canonical4264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4264 = injectiveMoment H node1162 := by
  calc
    injectiveMoment H raw4264 = injectiveMoment H raw4264step0 := by
      have heq : raw4264step0 = raw4264.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4264).symm
    injectiveMoment H raw4264step0 = injectiveMoment H raw4264step1 := by
      have heq : raw4264step1 = (fun i j => raw4264step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4264step0 permutation29 permutation20
    _ = injectiveMoment H node1162 := by rfl

theorem canonical4267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4267 = injectiveMoment H node2155 := by
  calc
    injectiveMoment H raw4267 = injectiveMoment H raw4267step0 := by
      have heq : raw4267step0 = (fun i j => raw4267 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4267 permutation39 permutation9
    _ = injectiveMoment H node2155 := by rfl

theorem canonical4268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4268 = injectiveMoment H node776 := by
  calc
    injectiveMoment H raw4268 = injectiveMoment H raw4268step0 := by
      have heq : raw4268step0 = raw4268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4268).symm
    injectiveMoment H raw4268step0 = injectiveMoment H raw4268step1 := by
      have heq : raw4268step1 = (fun i j => raw4268step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4268step0 permutation28 permutation24
    _ = injectiveMoment H node776 := by rfl

theorem canonical4270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4270 = injectiveMoment H node394 := by
  calc
    injectiveMoment H raw4270 = injectiveMoment H raw4270step0 := by
      have heq : raw4270step0 = raw4270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4270).symm
    injectiveMoment H raw4270step0 = injectiveMoment H raw4270step1 := by
      have heq : raw4270step1 = (fun i j => raw4270step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4270step0 permutation27 permutation18
    _ = injectiveMoment H node394 := by rfl

theorem canonical4276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4276 = injectiveMoment H node1184 := by
  calc
    injectiveMoment H raw4276 = injectiveMoment H raw4276step0 := by
      have heq : raw4276step0 = raw4276.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4276).symm
    injectiveMoment H raw4276step0 = injectiveMoment H raw4276step1 := by
      have heq : raw4276step1 = (fun i j => raw4276step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4276step0 permutation31 permutation26
    _ = injectiveMoment H node1184 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4357 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw4357 = injectiveMoment H raw4357step0 := by
      have heq : raw4357step0 = (fun i j => raw4357 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4357 permutation45 permutation11
    _ = injectiveMoment H node1507 := by rfl

theorem canonical4373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4373 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw4373 = injectiveMoment H raw4373step0 := by
      have heq : raw4373step0 = raw4373.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4373).symm
    injectiveMoment H raw4373step0 = injectiveMoment H raw4373step1 := by
      have heq : raw4373step1 = (fun i j => raw4373step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4373step0 permutation27 permutation18
    _ = injectiveMoment H node973 := by rfl

theorem canonical4377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4377 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw4377 = injectiveMoment H raw4377step0 := by
      have heq : raw4377step0 = raw4377.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4377).symm
    injectiveMoment H raw4377step0 = injectiveMoment H raw4377step1 := by
      have heq : raw4377step1 = (fun i j => raw4377step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4377step0 permutation27 permutation18
    _ = injectiveMoment H node804 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4394 = injectiveMoment H node808 := by
  calc
    injectiveMoment H raw4394 = injectiveMoment H raw4394step0 := by
      have heq : raw4394step0 = raw4394.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4394).symm
    injectiveMoment H raw4394step0 = injectiveMoment H raw4394step1 := by
      have heq : raw4394step1 = (fun i j => raw4394step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4394step0 permutation28 permutation24
    _ = injectiveMoment H node808 := by rfl

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

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5453 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5453 = injectiveMoment H raw5453step0 := by
      have heq : raw5453step0 = raw5453.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5453).symm
    injectiveMoment H raw5453step0 = injectiveMoment H raw5453step1 := by
      have heq : raw5453step1 = (fun i j => raw5453step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5453step0 permutation13 permutation1
    _ = injectiveMoment H node45 := by rfl

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5807 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw5807 = injectiveMoment H raw5807step0 := by
      have heq : raw5807step0 = raw5807.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5807).symm
    injectiveMoment H raw5807step0 = injectiveMoment H raw5807step1 := by
      have heq : raw5807step1 = (fun i j => raw5807step0 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5807step0 permutation11 permutation5
    _ = injectiveMoment H node84 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6091 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6091 = injectiveMoment H raw6091step0 := by
      have heq : raw6091step0 = raw6091.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6091).symm
    injectiveMoment H raw6091step0 = injectiveMoment H raw6091step1 := by
      have heq : raw6091step1 = (fun i j => raw6091step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6091step0 permutation27 permutation6
    _ = injectiveMoment H node145 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6283 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6283 = injectiveMoment H raw6283step0 := by
      have heq : raw6283step0 = raw6283.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6283).symm
    injectiveMoment H raw6283step0 = injectiveMoment H raw6283step1 := by
      have heq : raw6283step1 = (fun i j => raw6283step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6283step0 permutation27 permutation6
    _ = injectiveMoment H node271 := by rfl

theorem canonical6292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6292 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6292 = injectiveMoment H raw6292step0 := by
      have heq : raw6292step0 = raw6292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6292).symm
    injectiveMoment H raw6292step0 = injectiveMoment H raw6292step1 := by
      have heq : raw6292step1 = (fun i j => raw6292step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6292step0 permutation27 permutation6
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6858 = injectiveMoment H node61 := by
  rfl

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7257 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw7257 = injectiveMoment H raw7257step0 := by
      have heq : raw7257step0 = raw7257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7257).symm
    _ = injectiveMoment H node279 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7281 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7281 = injectiveMoment H raw7281step0 := by
      have heq : raw7281step0 = raw7281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7281).symm
    _ = injectiveMoment H node291 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7408 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7408 = injectiveMoment H raw7408step0 := by
      have heq : raw7408step0 = -raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7408).symm
    injectiveMoment H raw7408step0 = injectiveMoment H raw7408step1 := by
      have heq : raw7408step1 = (fun i j => raw7408step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7408step0 permutation8 permutation3
    _ = injectiveMoment H node53 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7457 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7457 = injectiveMoment H raw7457step0 := by
      have heq : raw7457step0 = -raw7457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7457).symm
    injectiveMoment H raw7457step0 = injectiveMoment H raw7457step1 := by
      have heq : raw7457step1 = (fun i j => raw7457step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7457step0 permutation8 permutation4
    _ = injectiveMoment H node62 := by rfl

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

theorem canonical7464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7464 = injectiveMoment H node257 := by
  calc
    injectiveMoment H raw7464 = injectiveMoment H raw7464step0 := by
      have heq : raw7464step0 = raw7464.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7464).symm
    injectiveMoment H raw7464step0 = injectiveMoment H raw7464step1 := by
      have heq : raw7464step1 = (fun i j => raw7464step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7464step0 permutation10 permutation3
    _ = injectiveMoment H node257 := by rfl

theorem canonical7468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7468 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7468 = injectiveMoment H raw7468step0 := by
      have heq : raw7468step0 = raw7468.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7468).symm
    injectiveMoment H raw7468step0 = injectiveMoment H raw7468step1 := by
      have heq : raw7468step1 = (fun i j => raw7468step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7468step0 permutation10 permutation3
    _ = injectiveMoment H node274 := by rfl

theorem canonical7478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7478 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw7478 = injectiveMoment H raw7478step0 := by
      have heq : raw7478step0 = raw7478.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7478).symm
    injectiveMoment H raw7478step0 = injectiveMoment H raw7478step1 := by
      have heq : raw7478step1 = (fun i j => raw7478step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7478step0 permutation13 permutation3
    _ = injectiveMoment H node288 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7521 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7521 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw7521 = injectiveMoment H raw7521step0 := by
      have heq : raw7521step0 = raw7521.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7521).symm
    injectiveMoment H raw7521step0 = injectiveMoment H raw7521step1 := by
      have heq : raw7521step1 = -raw7521step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7521step0).symm
    injectiveMoment H raw7521step1 = injectiveMoment H raw7521step2 := by
      have heq : raw7521step2 = (fun i j => raw7521step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7521step1 permutation24 permutation3
    _ = injectiveMoment H node195 := by rfl

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

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

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

theorem canonical8167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8167 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8167 = injectiveMoment H raw8167step0 := by
      have heq : raw8167step0 = (fun i j => raw8167 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8167 permutation5 permutation4
    _ = injectiveMoment H node62 := by rfl

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

theorem canonical8216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8216 = injectiveMoment H raw8216step0 := by
      have hz : ∀ j, raw8216 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8216step0 = (fun i j => raw8216 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8216 permutation7 hz
    injectiveMoment H raw8216step0 = injectiveMoment H raw8216step1 := by
      have hz : ∀ i, raw8216step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8216step1 = (fun i j => raw8216step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8216step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

theorem canonical8221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8221 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw8221 = injectiveMoment H raw8221step0 := by
      have heq : raw8221step0 = raw8221.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8221).symm
    injectiveMoment H raw8221step0 = injectiveMoment H raw8221step1 := by
      have heq : raw8221step1 = -raw8221step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8221step0).symm
    injectiveMoment H raw8221step1 = injectiveMoment H raw8221step2 := by
      have heq : raw8221step2 = (fun i j => raw8221step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8221step1 permutation25 permutation3
    _ = injectiveMoment H node193 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8226 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw8226 = injectiveMoment H raw8226step0 := by
      have heq : raw8226step0 = raw8226.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8226).symm
    injectiveMoment H raw8226step0 = injectiveMoment H raw8226step1 := by
      have heq : raw8226step1 = -raw8226step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8226step0).symm
    injectiveMoment H raw8226step1 = injectiveMoment H raw8226step2 := by
      have heq : raw8226step2 = (fun i j => raw8226step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8226step1 permutation25 permutation3
    _ = injectiveMoment H node198 := by rfl

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

theorem canonical842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw842 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw842 = injectiveMoment H raw842step0 := by
      have heq : raw842step0 = raw842.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw842).symm
    injectiveMoment H raw842step0 = injectiveMoment H raw842step1 := by
      have heq : raw842step1 = (fun i j => raw842step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw842step0 permutation13 permutation1
    _ = injectiveMoment H node25 := by rfl

theorem canonical843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw843 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw843 = injectiveMoment H raw843step0 := by
      have heq : raw843step0 = raw843.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw843).symm
    injectiveMoment H raw843step0 = injectiveMoment H raw843step1 := by
      have heq : raw843step1 = (fun i j => raw843step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw843step0 permutation13 permutation1
    _ = injectiveMoment H node23 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw955 = injectiveMoment H node27 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9955 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw9955 = injectiveMoment H raw9955step0 := by
      have heq : raw9955step0 = raw9955.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9955).symm
    injectiveMoment H raw9955step0 = injectiveMoment H raw9955step1 := by
      have heq : raw9955step1 = -raw9955step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9955step0).symm
    injectiveMoment H raw9955step1 = injectiveMoment H raw9955step2 := by
      have heq : raw9955step2 = (fun i j => raw9955step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9955step1 permutation23 permutation3
    _ = injectiveMoment H node193 := by rfl

theorem canonical9959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9959 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw9959 = injectiveMoment H raw9959step0 := by
      have heq : raw9959step0 = raw9959.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9959).symm
    injectiveMoment H raw9959step0 = injectiveMoment H raw9959step1 := by
      have heq : raw9959step1 = (fun i j => raw9959step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9959step0 permutation27 permutation3
    _ = injectiveMoment H node192 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1257 = injectiveMoment H node959 := by
  calc
    injectiveMoment H raw1257 = injectiveMoment H raw1257step0 := by
      have heq : raw1257step0 = raw1257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1257).symm
    injectiveMoment H raw1257step0 = injectiveMoment H raw1257step1 := by
      have heq : raw1257step1 = (fun i j => raw1257step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1257step0 permutation31 permutation18
    _ = injectiveMoment H node959 := by rfl

theorem canonical1259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1259 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1259 = injectiveMoment H raw1259step0 := by
      have heq : raw1259step0 = raw1259.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1259).symm
    injectiveMoment H raw1259step0 = injectiveMoment H raw1259step1 := by
      have heq : raw1259step1 = (fun i j => raw1259step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1259step0 permutation28 permutation18
    _ = injectiveMoment H node804 := by rfl

theorem canonical1265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1265 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1265 = injectiveMoment H raw1265step0 := by
      have heq : raw1265step0 = raw1265.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1265).symm
    injectiveMoment H raw1265step0 = injectiveMoment H raw1265step1 := by
      have heq : raw1265step1 = (fun i j => raw1265step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1265step0 permutation28 permutation24
    _ = injectiveMoment H node804 := by rfl

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

theorem canonical1320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1320 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1320 = injectiveMoment H raw1320step0 := by
      have heq : raw1320step0 = raw1320.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1320).symm
    injectiveMoment H raw1320step0 = injectiveMoment H raw1320step1 := by
      have heq : raw1320step1 = (fun i j => raw1320step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1320step0 permutation31 permutation18
    _ = injectiveMoment H node1027 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
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

theorem canonical181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw181 = injectiveMoment H node15 := by
  calc
    injectiveMoment H raw181 = injectiveMoment H raw181step0 := by
      have heq : raw181step0 = raw181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw181).symm
    injectiveMoment H raw181step0 = injectiveMoment H raw181step1 := by
      have heq : raw181step1 = (fun i j => raw181step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw181step0 permutation13 permutation1
    _ = injectiveMoment H node15 := by rfl

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

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node7 = Sparse.eval value7 (momentVector H) := by
  have hc : momentVector H 9 = injectiveMoment H node7 := rfl
  simp [value7, Sparse.eval, hc]

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
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

theorem sound15 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node15 = Sparse.eval value15 (momentVector H) := by
  have heq : pivotMatrix15 = (fun u v => node15 (pivotPermutation15 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node15 = injectiveMoment H pivotMatrix15 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix15 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix15 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix15 (0 : Fin 3)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (0 : Fin 3) = raw51 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical51 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix15 (1 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (1 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix15 (2 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (2 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node15 + (injectiveMoment H (mergeFirst pivotMatrix15 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix15 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix15 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value15, value7, value8, value9, Sparse.eval] at hc ⊢
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

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

theorem sound28 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node28 = Sparse.eval value28 (momentVector H) := by
  have hc : momentVector H 70 = injectiveMoment H node28 := rfl
  simp [value28, Sparse.eval, hc]

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
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

theorem sound61 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node61 = Sparse.eval value61 (momentVector H) := by
  have heq : pivotMatrix61 = (fun u v => node61 (pivotPermutation61 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node61 = injectiveMoment H pivotMatrix61 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix61 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix61 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (0 : Fin 2) = raw7462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7462 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node61 + (injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value61, value11, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound84 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node84 = Sparse.eval value84 (momentVector H) := by
  have hc : momentVector H 259 = injectiveMoment H node84 := rfl
  simp [value84, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node140 = Sparse.eval value140 (momentVector H) := by
  have heq : pivotMatrix140 = (fun u v => node140 (pivotPermutation140 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node140 = injectiveMoment H pivotMatrix140 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix140 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix140 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix140 (0 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix140 (0 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix140 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix140 (1 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix140 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix140 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node140 + (injectiveMoment H (mergeFirst pivotMatrix140 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix140 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix140 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value140, value27, value31, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node145 = Sparse.eval value145 (momentVector H) := by
  have heq : pivotMatrix145 = (fun u v => node145 (pivotPermutation145 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node145 = injectiveMoment H pivotMatrix145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix145 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix145 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (0 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node145 + (injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value145, value31, value52, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node152 = Sparse.eval value152 (momentVector H) := by
  have hc : momentVector H 308 = injectiveMoment H node152 := rfl
  simp [value152, Sparse.eval, hc]

theorem sound162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node162 = Sparse.eval value162 (momentVector H) := by
  have hc : momentVector H 124 = injectiveMoment H node162 := rfl
  simp [value162, Sparse.eval, hc]

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node184 = Sparse.eval value184 (momentVector H) := by
  have hc : momentVector H 51 = injectiveMoment H node184 := rfl
  simp [value184, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node192 = Sparse.eval value192 (momentVector H) := by
  have hc : momentVector H 196 = injectiveMoment H node192 := rfl
  simp [value192, Sparse.eval, hc]

theorem sound193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node193 = Sparse.eval value193 (momentVector H) := by
  have hc : momentVector H 723 = injectiveMoment H node193 := rfl
  simp [value193, Sparse.eval, hc]

theorem sound195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node195 = Sparse.eval value195 (momentVector H) := by
  have heq : pivotMatrix195 = (fun u v => node195 (pivotPermutation195 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node195 = injectiveMoment H pivotMatrix195 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix195 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix195 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix195 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix195 (0 : Fin 3) = raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7408 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix195 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix195 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix195 (2 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix195 (2 : Fin 3) = raw4015 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4015 hH).trans (sound28 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node195 + (injectiveMoment H (mergeFirst pivotMatrix195 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix195 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix195 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value195, value28, value32, value53, Sparse.eval] at hc ⊢
  linarith

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node257 = Sparse.eval value257 (momentVector H) := by
  have heq : pivotMatrix257 = (fun u v => node257.transpose (pivotPermutation257 u) v) := by apply Matrix.ext; unfold pivotMatrix257 node257 pivotPermutation257; decide +kernel
  have hmoment : injectiveMoment H node257 = injectiveMoment H pivotMatrix257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix257 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix257 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix257 (0 : Fin 2)) =
      Sparse.eval value15 (momentVector H) := by
    have heq : mergeFirst pivotMatrix257 (0 : Fin 2) = raw181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix257 raw181; decide +kernel
    rw [heq]
    exact (canonical181 hH).trans (sound15 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix257 (1 : Fin 2)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix257 (1 : Fin 2) = raw843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix257 raw843; decide +kernel
    rw [heq]
    exact (canonical843 hH).trans (sound23 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node257 + (injectiveMoment H (mergeFirst pivotMatrix257 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix257 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value257, value15, value23, Sparse.eval] at hc ⊢
  linarith

theorem sound271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node271 = Sparse.eval value271 (momentVector H) := by
  have heq : pivotMatrix271 = (fun u v => node271 (pivotPermutation271 u) v) := by apply Matrix.ext; unfold pivotMatrix271 node271 pivotPermutation271; decide +kernel
  have hmoment : injectiveMoment H node271 = injectiveMoment H pivotMatrix271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix271 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix271 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (2 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node271 + (injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value271, value56, value57, value61, Sparse.eval] at hc ⊢
  linarith

theorem sound274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node274 = Sparse.eval value274 (momentVector H) := by
  have heq : pivotMatrix274 = (fun u v => node274.transpose (pivotPermutation274 u) v) := by apply Matrix.ext; unfold pivotMatrix274 node274 pivotPermutation274; decide +kernel
  have hmoment : injectiveMoment H node274 = injectiveMoment H pivotMatrix274 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix274 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix274 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix274 (0 : Fin 2)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix274 (0 : Fin 2) = raw842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix274 raw842; decide +kernel
    rw [heq]
    exact (canonical842 hH).trans (sound25 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix274 (1 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix274 (1 : Fin 2) = raw5453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix274 raw5453; decide +kernel
    rw [heq]
    exact (canonical5453 hH).trans (sound45 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node274 + (injectiveMoment H (mergeFirst pivotMatrix274 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix274 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value274, value25, value45, Sparse.eval] at hc ⊢
  linarith

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

theorem sound288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node288 = Sparse.eval value288 (momentVector H) := by
  have heq : pivotMatrix288 = (fun u v => node288 (pivotPermutation288 u) v) := by apply Matrix.ext; unfold pivotMatrix288 node288 pivotPermutation288; decide +kernel
  have hmoment : injectiveMoment H node288 = injectiveMoment H pivotMatrix288 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix288 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix288 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix288 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (0 : Fin 3) = raw7457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw7457; decide +kernel
    rw [heq]
    exact (canonical7457 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix288 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (1 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix288 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (2 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node288 + (injectiveMoment H (mergeFirst pivotMatrix288 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix288 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix288 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value288, value62, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node291 = Sparse.eval value291 (momentVector H) := by
  have heq : pivotMatrix291 = (fun u v => node291 (pivotPermutation291 u) v) := by apply Matrix.ext; unfold pivotMatrix291 node291 pivotPermutation291; decide +kernel
  have hmoment : injectiveMoment H node291 = injectiveMoment H pivotMatrix291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix291 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix291 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (1 : Fin 3) = raw8167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8167; decide +kernel
    rw [heq]
    exact (canonical8167 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (2 : Fin 3) = raw8216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8216; decide +kernel
    rw [heq]
    exact (canonical8216 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node291 + (injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value291, value4, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound770 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node770 = Sparse.eval value770 (momentVector H) := by
  have heq : pivotMatrix770 = (fun u v => node770.transpose (pivotPermutation770 u) v) := by apply Matrix.ext; unfold pivotMatrix770 node770 pivotPermutation770; decide +kernel
  have hmoment : injectiveMoment H node770 = injectiveMoment H pivotMatrix770 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix770 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix770 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix770 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix770 (0 : Fin 3) = raw340 := by apply Matrix.ext; unfold mergeFirst pivotMatrix770 raw340; decide +kernel
    rw [heq]
    exact (canonical340 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix770 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix770 (1 : Fin 3) = raw3645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix770 raw3645; decide +kernel
    rw [heq]
    exact (canonical3645 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix770 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix770 (2 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix770 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node770 + (injectiveMoment H (mergeFirst pivotMatrix770 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix770 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix770 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value770, value152, value184, value84, Sparse.eval] at hc ⊢
  linarith

theorem sound776 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node776 = Sparse.eval value776 (momentVector H) := by
  have heq : pivotMatrix776 = (fun u v => node776.transpose (pivotPermutation776 u) v) := by apply Matrix.ext; unfold pivotMatrix776 node776 pivotPermutation776; decide +kernel
  have hmoment : injectiveMoment H node776 = injectiveMoment H pivotMatrix776 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix776 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix776 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix776 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (0 : Fin 3) = raw357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw357; decide +kernel
    rw [heq]
    exact (canonical357 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix776 (1 : Fin 3)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (1 : Fin 3) = raw4167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw4167; decide +kernel
    rw [heq]
    exact (canonical4167 hH).trans (sound140 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix776 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (2 : Fin 3) = raw4173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw4173; decide +kernel
    rw [heq]
    exact (canonical4173 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node776 + (injectiveMoment H (mergeFirst pivotMatrix776 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix776 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix776 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value776, value140, value162, value84, Sparse.eval] at hc ⊢
  linarith

theorem sound804 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node804 = Sparse.eval value804 (momentVector H) := by
  have heq : pivotMatrix804 = (fun u v => node804.transpose (pivotPermutation804 u) v) := by apply Matrix.ext; unfold pivotMatrix804 node804 pivotPermutation804; decide +kernel
  have hmoment : injectiveMoment H node804 = injectiveMoment H pivotMatrix804 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix804 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix804 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix804 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (0 : Fin 3) = raw346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw346; decide +kernel
    rw [heq]
    exact (canonical346 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix804 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (1 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix804 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (2 : Fin 3) = raw3847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw3847; decide +kernel
    rw [heq]
    exact (canonical3847 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node804 + (injectiveMoment H (mergeFirst pivotMatrix804 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix804 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix804 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value804, value184, value198, value203, Sparse.eval] at hc ⊢
  linarith

theorem sound808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node808 = Sparse.eval value808 (momentVector H) := by
  have heq : pivotMatrix808 = (fun u v => node808.transpose (pivotPermutation808 u) v) := by apply Matrix.ext; unfold pivotMatrix808 node808 pivotPermutation808; decide +kernel
  have hmoment : injectiveMoment H node808 = injectiveMoment H pivotMatrix808 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix808 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix808 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix808 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix808 (0 : Fin 3) = raw362 := by apply Matrix.ext; unfold mergeFirst pivotMatrix808 raw362; decide +kernel
    rw [heq]
    exact (canonical362 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix808 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix808 (1 : Fin 3) = raw4172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix808 raw4172; decide +kernel
    rw [heq]
    exact (canonical4172 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix808 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix808 (2 : Fin 3) = raw4197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix808 raw4197; decide +kernel
    rw [heq]
    exact (canonical4197 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node808 + (injectiveMoment H (mergeFirst pivotMatrix808 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix808 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix808 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value808, value169, value197, value198, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound913 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node913 = Sparse.eval value913 (momentVector H) := by
  have heq : pivotMatrix913 = (fun u v => node913.transpose (pivotPermutation913 u) v) := by apply Matrix.ext; unfold pivotMatrix913 node913 pivotPermutation913; decide +kernel
  have hmoment : injectiveMoment H node913 = injectiveMoment H pivotMatrix913 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix913 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix913 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix913 (0 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix913 (0 : Fin 3) = raw3645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix913 raw3645; decide +kernel
    rw [heq]
    exact (canonical3645 hH).trans (sound152 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix913 (1 : Fin 3)) =
      Sparse.eval value257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix913 (1 : Fin 3) = raw7464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix913 raw7464; decide +kernel
    rw [heq]
    exact (canonical7464 hH).trans (sound257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix913 (2 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix913 (2 : Fin 3) = raw7468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix913 raw7468; decide +kernel
    rw [heq]
    exact (canonical7468 hH).trans (sound274 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node913 + (injectiveMoment H (mergeFirst pivotMatrix913 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix913 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix913 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value913, value152, value257, value274, Sparse.eval] at hc ⊢
  linarith

theorem sound959 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node959 = Sparse.eval value959 (momentVector H) := by
  have heq : pivotMatrix959 = (fun u v => node959 (pivotPermutation959 u) v) := by apply Matrix.ext; unfold pivotMatrix959 node959 pivotPermutation959; decide +kernel
  have hmoment : injectiveMoment H node959 = injectiveMoment H pivotMatrix959 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix959 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix959 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix959 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix959 (0 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix959 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix959 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix959 (1 : Fin 3) = raw6283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix959 raw6283; decide +kernel
    rw [heq]
    exact (canonical6283 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix959 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix959 (2 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix959 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node959 + (injectiveMoment H (mergeFirst pivotMatrix959 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix959 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix959 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value959, value145, value176, value271, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound973 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node973 = Sparse.eval value973 (momentVector H) := by
  have heq : pivotMatrix973 = (fun u v => node973.transpose (pivotPermutation973 u) v) := by apply Matrix.ext; unfold pivotMatrix973 node973 pivotPermutation973; decide +kernel
  have hmoment : injectiveMoment H node973 = injectiveMoment H pivotMatrix973 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix973 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix973 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix973 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (0 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix973 (1 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (1 : Fin 3) = raw7468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw7468; decide +kernel
    rw [heq]
    exact (canonical7468 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix973 (2 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (2 : Fin 3) = raw7478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw7478; decide +kernel
    rw [heq]
    exact (canonical7478 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node973 + (injectiveMoment H (mergeFirst pivotMatrix973 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix973 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix973 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value973, value184, value274, value288, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1027 = Sparse.eval value1027 (momentVector H) := by
  have heq : pivotMatrix1027 = (fun u v => node1027.transpose (pivotPermutation1027 u) v) := by apply Matrix.ext; unfold pivotMatrix1027 node1027 pivotPermutation1027; decide +kernel
  have hmoment : injectiveMoment H node1027 = injectiveMoment H pivotMatrix1027 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1027 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1027 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (0 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (1 : Fin 3) = raw7257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7257; decide +kernel
    rw [heq]
    exact (canonical7257 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (2 : Fin 3) = raw7281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7281; decide +kernel
    rw [heq]
    exact (canonical7281 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1027 + (injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1027, value197, value279, value291, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1162 = Sparse.eval value1162 (momentVector H) := by
  have heq : pivotMatrix1162 = (fun u v => node1162.transpose (pivotPermutation1162 u) v) := by apply Matrix.ext; unfold pivotMatrix1162 node1162 pivotPermutation1162; decide +kernel
  have hmoment : injectiveMoment H node1162 = injectiveMoment H pivotMatrix1162 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1162 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1162 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1162 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1162 (0 : Fin 3) = raw5807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1162 raw5807; decide +kernel
    rw [heq]
    exact (canonical5807 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1162 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1162 (1 : Fin 3) = raw8221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1162 raw8221; decide +kernel
    rw [heq]
    exact (canonical8221 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1162 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1162 (2 : Fin 3) = raw8226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1162 raw8226; decide +kernel
    rw [heq]
    exact (canonical8226 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1162 + (injectiveMoment H (mergeFirst pivotMatrix1162 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1162 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1162 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1162, value193, value198, value84, Sparse.eval] at hc ⊢
  linarith

theorem sound1184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1184 = Sparse.eval value1184 (momentVector H) := by
  have heq : pivotMatrix1184 = (fun u v => node1184.transpose (pivotPermutation1184 u) v) := by apply Matrix.ext; unfold pivotMatrix1184 node1184 pivotPermutation1184; decide +kernel
  have hmoment : injectiveMoment H node1184 = injectiveMoment H pivotMatrix1184 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1184 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1184 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1184 (0 : Fin 3)) =
      Sparse.eval value195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1184 (0 : Fin 3) = raw7521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1184 raw7521; decide +kernel
    rw [heq]
    exact (canonical7521 hH).trans (sound195 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1184 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1184 (1 : Fin 3) = raw9955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1184 raw9955; decide +kernel
    rw [heq]
    exact (canonical9955 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1184 (2 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1184 (2 : Fin 3) = raw9959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1184 raw9959; decide +kernel
    rw [heq]
    exact (canonical9959 hH).trans (sound192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1184 + (injectiveMoment H (mergeFirst pivotMatrix1184 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1184 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1184 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1184, value192, value193, value195, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound6
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node394 = Sparse.eval value394 (momentVector H) := by
  have hc : momentVector H 282 = injectiveMoment H node394 := rfl
  simp [value394, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound23
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1507 = Sparse.eval value1507 (momentVector H) := by
  have heq : pivotMatrix1507 = (fun u v => node1507 (pivotPermutation1507 u) v) := by apply Matrix.ext; unfold pivotMatrix1507 node1507 pivotPermutation1507; decide +kernel
  have hmoment : injectiveMoment H node1507 = injectiveMoment H pivotMatrix1507 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1507 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1507 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1507 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (0 : Fin 4) = raw1320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1320; decide +kernel
    rw [heq]
    exact (canonical1320 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1507 (1 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (1 : Fin 4) = raw1265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1265; decide +kernel
    rw [heq]
    exact (canonical1265 hH).trans (sound804 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1507 (2 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (2 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1507 (3 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (3 : Fin 4) = raw1257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1257; decide +kernel
    rw [heq]
    exact (canonical1257 hH).trans (sound959 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1507 + (injectiveMoment H (mergeFirst pivotMatrix1507 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1507 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1507 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1507 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1507, value1027, value804, value959, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound33
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2153 = Sparse.eval value2153 (momentVector H) := by
  have heq : pivotMatrix2153 = (fun u v => node2153 (pivotPermutation2153 u) v) := by apply Matrix.ext; unfold pivotMatrix2153 node2153 pivotPermutation2153; decide +kernel
  have hmoment : injectiveMoment H node2153 = injectiveMoment H pivotMatrix2153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2153 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2153 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2153 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (0 : Fin 4) = raw4373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4373; decide +kernel
    rw [heq]
    exact (canonical4373 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2153 (1 : Fin 4)) =
      Sparse.eval value776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (1 : Fin 4) = raw4268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4268; decide +kernel
    rw [heq]
    exact (canonical4268 hH).trans (sound776 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2153 (2 : Fin 4)) =
      Sparse.eval value770 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (2 : Fin 4) = raw4262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4262; decide +kernel
    rw [heq]
    exact (canonical4262 hH).trans (sound770 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2153 (3 : Fin 4)) =
      Sparse.eval value913 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (3 : Fin 4) = raw4260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4260; decide +kernel
    rw [heq]
    exact (canonical4260 hH).trans (sound913 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2153 + (injectiveMoment H (mergeFirst pivotMatrix2153 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2153 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2153 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2153 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2153, value770, value776, value913, value973, Sparse.eval] at hc ⊢
  linarith

theorem sound2154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2154 = Sparse.eval value2154 (momentVector H) := by
  have heq : pivotMatrix2154 = (fun u v => node2154 (pivotPermutation2154 u) v) := by apply Matrix.ext; unfold pivotMatrix2154 node2154 pivotPermutation2154; decide +kernel
  have hmoment : injectiveMoment H node2154 = injectiveMoment H pivotMatrix2154 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2154 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2154 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2154 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (0 : Fin 4) = raw4377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4377; decide +kernel
    rw [heq]
    exact (canonical4377 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2154 (1 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (1 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2154 (2 : Fin 4)) =
      Sparse.eval value1162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (2 : Fin 4) = raw4264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4264; decide +kernel
    rw [heq]
    exact (canonical4264 hH).trans (sound1162 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2154 (3 : Fin 4)) =
      Sparse.eval value770 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (3 : Fin 4) = raw4262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4262; decide +kernel
    rw [heq]
    exact (canonical4262 hH).trans (sound770 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2154 + (injectiveMoment H (mergeFirst pivotMatrix2154 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2154 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2154 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2154 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2154, value1162, value394, value770, value804, Sparse.eval] at hc ⊢
  linarith

theorem sound2155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2155 = Sparse.eval value2155 (momentVector H) := by
  have heq : pivotMatrix2155 = (fun u v => node2155 (pivotPermutation2155 u) v) := by apply Matrix.ext; unfold pivotMatrix2155 node2155 pivotPermutation2155; decide +kernel
  have hmoment : injectiveMoment H node2155 = injectiveMoment H pivotMatrix2155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2155 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2155 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2155 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (0 : Fin 4) = raw4394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4394; decide +kernel
    rw [heq]
    exact (canonical4394 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2155 (1 : Fin 4)) =
      Sparse.eval value1184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (1 : Fin 4) = raw4276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4276; decide +kernel
    rw [heq]
    exact (canonical4276 hH).trans (sound1184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2155 (2 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (2 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2155 (3 : Fin 4)) =
      Sparse.eval value776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (3 : Fin 4) = raw4268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4268; decide +kernel
    rw [heq]
    exact (canonical4268 hH).trans (sound776 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2155 + (injectiveMoment H (mergeFirst pivotMatrix2155 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2155 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2155 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2155 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2155, value1184, value394, value776, value808, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound50
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3223_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3223 = Sparse.eval value3223 (momentVector H) := by
  have heq : pivotMatrix3223 = (fun u v => node3223 (pivotPermutation3223 u) v) := by apply Matrix.ext; unfold pivotMatrix3223 node3223 pivotPermutation3223; decide +kernel
  have hmoment : injectiveMoment H node3223 = injectiveMoment H pivotMatrix3223 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3223 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3223 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3223 (0 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3223 (0 : Fin 5) = raw4357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3223 raw4357; decide +kernel
    rw [heq]
    exact (canonical4357 hH).trans (sound1507 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3223 (1 : Fin 5)) =
      Sparse.eval value2155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3223 (1 : Fin 5) = raw4267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3223 raw4267; decide +kernel
    rw [heq]
    exact (canonical4267 hH).trans (sound2155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3223 (2 : Fin 5)) =
      Sparse.eval value2155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3223 (2 : Fin 5) = raw4258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3223 raw4258; decide +kernel
    rw [heq]
    exact (canonical4258 hH).trans (sound2155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3223 (3 : Fin 5)) =
      Sparse.eval value2154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3223 (3 : Fin 5) = raw4257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3223 raw4257; decide +kernel
    rw [heq]
    exact (canonical4257 hH).trans (sound2154 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3223 (4 : Fin 5)) =
      Sparse.eval value2153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3223 (4 : Fin 5) = raw4256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3223 raw4256; decide +kernel
    rw [heq]
    exact (canonical4256 hH).trans (sound2153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3223 + (injectiveMoment H (mergeFirst pivotMatrix3223 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3223 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3223 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3223 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3223 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3223, value1507, value2153, value2154, value2155, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3223_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3223_e_oai
