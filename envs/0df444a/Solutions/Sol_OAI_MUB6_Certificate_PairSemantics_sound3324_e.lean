-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3324_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T10:24:35.131177+00:00
-- url     : https://prove2.me/submissions/2c727c57-18a2-4664-831a-55695cb57ba5

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

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

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5243 = injectiveMoment H node1014 := by
  calc
    injectiveMoment H raw5243 = injectiveMoment H raw5243step0 := by
      have heq : raw5243step0 = raw5243.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5243).symm
    injectiveMoment H raw5243step0 = injectiveMoment H raw5243step1 := by
      have heq : raw5243step1 = (fun i j => raw5243step0 (permutation18 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5243step0 permutation18 permutation24
    _ = injectiveMoment H node1014 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5305 = injectiveMoment H node1154 := by
  calc
    injectiveMoment H raw5305 = injectiveMoment H raw5305step0 := by
      have heq : raw5305step0 = raw5305.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5305).symm
    injectiveMoment H raw5305step0 = injectiveMoment H raw5305step1 := by
      have heq : raw5305step1 = (fun i j => raw5305step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5305step0 permutation18 permutation23
    _ = injectiveMoment H node1154 := by rfl

theorem canonical5308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5308 = injectiveMoment H node453 := by
  calc
    injectiveMoment H raw5308 = injectiveMoment H raw5308step0 := by
      have heq : raw5308step0 = raw5308.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5308).symm
    injectiveMoment H raw5308step0 = injectiveMoment H raw5308step1 := by
      have heq : raw5308step1 = -raw5308step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5308step0).symm
    injectiveMoment H raw5308step1 = injectiveMoment H raw5308step2 := by
      have heq : raw5308step2 = (fun i j => raw5308step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5308step1 permutation27 permutation17
    _ = injectiveMoment H node453 := by rfl

theorem canonical5309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5309 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw5309 = injectiveMoment H raw5309step0 := by
      have heq : raw5309step0 = raw5309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5309).symm
    injectiveMoment H raw5309step0 = injectiveMoment H raw5309step1 := by
      have heq : raw5309step1 = (fun i j => raw5309step0 (permutation18 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5309step0 permutation18 permutation24
    _ = injectiveMoment H node1007 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5389 = injectiveMoment H node2364 := by
  rfl

theorem canonical5390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5390 = injectiveMoment H node2365 := by
  rfl

theorem canonical5393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5393 = injectiveMoment H node2367 := by
  rfl

theorem canonical5395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5395 = injectiveMoment H node576 := by
  calc
    injectiveMoment H raw5395 = injectiveMoment H raw5395step0 := by
      have heq : raw5395step0 = raw5395.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5395).symm
    injectiveMoment H raw5395step0 = injectiveMoment H raw5395step1 := by
      have heq : raw5395step1 = (fun i j => raw5395step0 (permutation27 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5395step0 permutation27 permutation22
    _ = injectiveMoment H node576 := by rfl

theorem canonical5396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5396 = injectiveMoment H node1373 := by
  calc
    injectiveMoment H raw5396 = injectiveMoment H raw5396step0 := by
      have heq : raw5396step0 = raw5396.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5396).symm
    injectiveMoment H raw5396step0 = injectiveMoment H raw5396step1 := by
      have heq : raw5396step1 = (fun i j => raw5396step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5396step0 permutation18 permutation21
    _ = injectiveMoment H node1373 := by rfl

theorem canonical5397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5397 = injectiveMoment H node688 := by
  calc
    injectiveMoment H raw5397 = injectiveMoment H raw5397step0 := by
      have heq : raw5397step0 = raw5397.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5397).symm
    injectiveMoment H raw5397step0 = injectiveMoment H raw5397step1 := by
      have heq : raw5397step1 = -raw5397step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5397step0).symm
    injectiveMoment H raw5397step1 = injectiveMoment H raw5397step2 := by
      have heq : raw5397step2 = (fun i j => raw5397step1 (permutation18 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5397step1 permutation18 permutation12
    _ = injectiveMoment H node688 := by rfl

theorem canonical5398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5398 = injectiveMoment H node584 := by
  calc
    injectiveMoment H raw5398 = injectiveMoment H raw5398step0 := by
      have heq : raw5398step0 = raw5398.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5398).symm
    injectiveMoment H raw5398step0 = injectiveMoment H raw5398step1 := by
      have heq : raw5398step1 = (fun i j => raw5398step0 (permutation29 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5398step0 permutation29 permutation28
    _ = injectiveMoment H node584 := by rfl

theorem canonical5401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5401 = injectiveMoment H node1642 := by
  calc
    injectiveMoment H raw5401 = injectiveMoment H raw5401step0 := by
      have heq : raw5401step0 = (fun i j => raw5401 (permutation68 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5401 permutation68 permutation23
    _ = injectiveMoment H node1642 := by rfl

theorem canonical5403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5403 = injectiveMoment H node1374 := by
  calc
    injectiveMoment H raw5403 = injectiveMoment H raw5403step0 := by
      have heq : raw5403step0 = raw5403.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5403).symm
    injectiveMoment H raw5403step0 = injectiveMoment H raw5403step1 := by
      have heq : raw5403step1 = (fun i j => raw5403step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5403step0 permutation18 permutation21
    _ = injectiveMoment H node1374 := by rfl

theorem canonical5404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5404 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw5404 = injectiveMoment H raw5404step0 := by
      have heq : raw5404step0 = raw5404.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5404).symm
    injectiveMoment H raw5404step0 = injectiveMoment H raw5404step1 := by
      have heq : raw5404step1 = (fun i j => raw5404step0 (permutation29 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5404step0 permutation29 permutation31
    _ = injectiveMoment H node476 := by rfl

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

theorem canonical5443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5443 = injectiveMoment H node394 := by
  calc
    injectiveMoment H raw5443 = injectiveMoment H raw5443step0 := by
      have heq : raw5443step0 = raw5443.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5443).symm
    injectiveMoment H raw5443step0 = injectiveMoment H raw5443step1 := by
      have heq : raw5443step1 = (fun i j => raw5443step0 (permutation29 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5443step0 permutation29 permutation25
    _ = injectiveMoment H node394 := by rfl

theorem canonical5446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5446 = injectiveMoment H node2348 := by
  calc
    injectiveMoment H raw5446 = injectiveMoment H raw5446step0 := by
      have heq : raw5446step0 = -raw5446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5446).symm
    injectiveMoment H raw5446step0 = injectiveMoment H raw5446step1 := by
      have heq : raw5446step1 = (fun i j => raw5446step0 (permutation54 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5446step0 permutation54 permutation15
    _ = injectiveMoment H node2348 := by rfl

theorem canonical5448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5448 = injectiveMoment H node1154 := by
  calc
    injectiveMoment H raw5448 = injectiveMoment H raw5448step0 := by
      have heq : raw5448step0 = raw5448.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5448).symm
    injectiveMoment H raw5448step0 = injectiveMoment H raw5448step1 := by
      have heq : raw5448step1 = -raw5448step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5448step0).symm
    injectiveMoment H raw5448step1 = injectiveMoment H raw5448step2 := by
      have heq : raw5448step2 = (fun i j => raw5448step1 (permutation12 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5448step1 permutation12 permutation25
    _ = injectiveMoment H node1154 := by rfl

theorem canonical5449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5449 = injectiveMoment H node453 := by
  calc
    injectiveMoment H raw5449 = injectiveMoment H raw5449step0 := by
      have heq : raw5449step0 = raw5449.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5449).symm
    injectiveMoment H raw5449step0 = injectiveMoment H raw5449step1 := by
      have heq : raw5449step1 = (fun i j => raw5449step0 (permutation29 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5449step0 permutation29 permutation31
    _ = injectiveMoment H node453 := by rfl

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

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

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

theorem canonical5540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5540 = injectiveMoment H node51 := by
  rfl

theorem canonical5552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5552 = injectiveMoment H node54 := by
  rfl

theorem canonical5554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5554 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5554 = injectiveMoment H raw5554step0 := by
      have heq : raw5554step0 = (fun i j => raw5554 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5554 permutation4 permutation3
    _ = injectiveMoment H node53 := by rfl

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

theorem canonical5813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5813 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5813 = injectiveMoment H raw5813step0 := by
      have heq : raw5813step0 = raw5813.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5813).symm
    injectiveMoment H raw5813step0 = injectiveMoment H raw5813step1 := by
      have heq : raw5813step1 = -raw5813step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5813step0).symm
    injectiveMoment H raw5813step1 = injectiveMoment H raw5813step2 := by
      have heq : raw5813step2 = (fun i j => raw5813step1 (permutation9 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5813step1 permutation9 permutation7
    _ = injectiveMoment H node111 := by rfl

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

theorem canonical5982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5982 = injectiveMoment H node58 := by
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

theorem canonical5996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5996 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw5996 = injectiveMoment H raw5996step0 := by
      have heq : raw5996step0 = raw5996.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5996).symm
    injectiveMoment H raw5996step0 = injectiveMoment H raw5996step1 := by
      have heq : raw5996step1 = -raw5996step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5996step0).symm
    injectiveMoment H raw5996step1 = injectiveMoment H raw5996step2 := by
      have heq : raw5996step2 = (fun i j => raw5996step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5996step1 permutation22 permutation5
    _ = injectiveMoment H node243 := by rfl

theorem canonical5997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5997 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw5997 = injectiveMoment H raw5997step0 := by
      have heq : raw5997step0 = raw5997.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5997).symm
    injectiveMoment H raw5997step0 = injectiveMoment H raw5997step1 := by
      have heq : raw5997step1 = -raw5997step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5997step0).symm
    injectiveMoment H raw5997step1 = injectiveMoment H raw5997step2 := by
      have heq : raw5997step2 = (fun i j => raw5997step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5997step1 permutation25 permutation3
    _ = injectiveMoment H node84 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6324 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6324 = injectiveMoment H raw6324step0 := by
      have heq : raw6324step0 = raw6324.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6324).symm
    injectiveMoment H raw6324step0 = injectiveMoment H raw6324step1 := by
      have heq : raw6324step1 = (fun i j => raw6324step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6324step0 permutation28 permutation6
    _ = injectiveMoment H node271 := by rfl

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

theorem canonical6905 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6905 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6905 = injectiveMoment H raw6905step0 := by
      have heq : raw6905step0 = raw6905.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6905).symm
    injectiveMoment H raw6905step0 = injectiveMoment H raw6905step1 := by
      have heq : raw6905step1 = -raw6905step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6905step0).symm
    injectiveMoment H raw6905step1 = injectiveMoment H raw6905step2 := by
      have heq : raw6905step2 = (fun i j => raw6905step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6905step1 permutation25 permutation4
    _ = injectiveMoment H node184 := by rfl

theorem canonical6909 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6909 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw6909 = injectiveMoment H raw6909step0 := by
      have heq : raw6909step0 = raw6909.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6909).symm
    injectiveMoment H raw6909step0 = injectiveMoment H raw6909step1 := by
      have heq : raw6909step1 = -raw6909step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6909step0).symm
    injectiveMoment H raw6909step1 = injectiveMoment H raw6909step2 := by
      have heq : raw6909step2 = (fun i j => raw6909step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6909step1 permutation25 permutation4
    _ = injectiveMoment H node152 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6934 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6934 = injectiveMoment H raw6934step0 := by
      have heq : raw6934step0 = raw6934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6934).symm
    injectiveMoment H raw6934step0 = injectiveMoment H raw6934step1 := by
      have heq : raw6934step1 = -raw6934step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6934step0).symm
    injectiveMoment H raw6934step1 = injectiveMoment H raw6934step2 := by
      have heq : raw6934step2 = (fun i j => raw6934step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6934step1 permutation25 permutation4
    _ = injectiveMoment H node181 := by rfl

theorem canonical6937 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6937 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw6937 = injectiveMoment H raw6937step0 := by
      have heq : raw6937step0 = raw6937.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6937).symm
    injectiveMoment H raw6937step0 = injectiveMoment H raw6937step1 := by
      have heq : raw6937step1 = -raw6937step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6937step0).symm
    injectiveMoment H raw6937step1 = injectiveMoment H raw6937step2 := by
      have heq : raw6937step2 = (fun i j => raw6937step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6937step1 permutation25 permutation4
    _ = injectiveMoment H node149 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7021 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw7021 = injectiveMoment H raw7021step0 := by
      have hz : ∀ i, raw7021 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7021step0 = (fun i j => raw7021 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7021 permutation15 hz
    _ = injectiveMoment H node52 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7041 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw7041 = injectiveMoment H raw7041step0 := by
      have heq : raw7041step0 = raw7041.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7041).symm
    injectiveMoment H raw7041step0 = injectiveMoment H raw7041step1 := by
      have heq : raw7041step1 = (fun i j => raw7041step0 (permutation27 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7041step0 permutation27 permutation8
    _ = injectiveMoment H node149 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7101 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw7101 = injectiveMoment H raw7101step0 := by
      have hz : ∀ i, raw7101 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7101step0 = (fun i j => raw7101 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7101 permutation15 hz
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7117 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7117 = injectiveMoment H raw7117step0 := by
      have heq : raw7117step0 = raw7117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7117).symm
    injectiveMoment H raw7117step0 = injectiveMoment H raw7117step1 := by
      have heq : raw7117step1 = (fun i j => raw7117step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7117step0 permutation28 permutation6
    _ = injectiveMoment H node272 := by rfl

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

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7896 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7896 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw7896 = injectiveMoment H raw7896step0 := by
      have heq : raw7896step0 = (fun i j => raw7896 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7896 permutation18 permutation15
    _ = injectiveMoment H node1178 := by rfl

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

theorem canonical7988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7988 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw7988 = injectiveMoment H raw7988step0 := by
      have hz : ∀ i, raw7988 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7988step0 = (fun i j => raw7988 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7988 permutation3 hz
    _ = injectiveMoment H node2 := by rfl

theorem canonical7997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7997 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7997 = injectiveMoment H raw7997step0 := by
      have heq : raw7997step0 = (fun i j => raw7997 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7997 permutation5 permutation4
    _ = injectiveMoment H node53 := by rfl

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

theorem canonical8007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8007 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw8007 = injectiveMoment H raw8007step0 := by
      have hz : ∀ i, raw8007 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8007step0 = (fun i j => raw8007 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8007 permutation3 hz
    injectiveMoment H raw8007step0 = injectiveMoment H raw8007step1 := by
      have heq : raw8007step1 = (fun i j => raw8007step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8007step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

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

theorem canonical8169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8169 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw8169 = injectiveMoment H raw8169step0 := by
      have heq : raw8169step0 = (fun i j => raw8169 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8169 permutation5 permutation4
    _ = injectiveMoment H node57 := by rfl

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

theorem canonical8217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8217 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8217 = injectiveMoment H raw8217step0 := by
      have hz : ∀ i, raw8217 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8217step0 = (fun i j => raw8217 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8217 permutation3 hz
    injectiveMoment H raw8217step0 = injectiveMoment H raw8217step1 := by
      have heq : raw8217step1 = (fun i j => raw8217step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8217step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical8227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8227 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw8227 = injectiveMoment H raw8227step0 := by
      have heq : raw8227step0 = raw8227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8227).symm
    injectiveMoment H raw8227step0 = injectiveMoment H raw8227step1 := by
      have heq : raw8227step1 = (fun i j => raw8227step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8227step0 permutation19 permutation4
    _ = injectiveMoment H node198 := by rfl

theorem canonical8235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8235 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw8235 = injectiveMoment H raw8235step0 := by
      have heq : raw8235step0 = raw8235.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8235).symm
    injectiveMoment H raw8235step0 = injectiveMoment H raw8235step1 := by
      have heq : raw8235step1 = (fun i j => raw8235step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8235step0 permutation19 permutation4
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8286 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8286 = injectiveMoment H raw8286step0 := by
      have hz : ∀ i, raw8286 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8286step0 = (fun i j => raw8286 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8286 permutation9 hz
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10139 = injectiveMoment H node290 := by
  calc
    injectiveMoment H raw10139 = injectiveMoment H raw10139step0 := by
      have heq : raw10139step0 = raw10139.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10139).symm
    injectiveMoment H raw10139step0 = injectiveMoment H raw10139step1 := by
      have heq : raw10139step1 = (fun i j => raw10139step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10139step0 permutation30 permutation3
    _ = injectiveMoment H node290 := by rfl

theorem canonical10141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10141 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw10141 = injectiveMoment H raw10141step0 := by
      have heq : raw10141step0 = raw10141.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10141).symm
    injectiveMoment H raw10141step0 = injectiveMoment H raw10141step1 := by
      have heq : raw10141step1 = (fun i j => raw10141step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10141step0 permutation30 permutation3
    _ = injectiveMoment H node292 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10176 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw10176 = injectiveMoment H raw10176step0 := by
      have heq : raw10176step0 = raw10176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10176).symm
    injectiveMoment H raw10176step0 = injectiveMoment H raw10176step1 := by
      have heq : raw10176step1 = -raw10176step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10176step0).symm
    injectiveMoment H raw10176step1 = injectiveMoment H raw10176step2 := by
      have heq : raw10176step2 = (fun i j => raw10176step1 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10176step1 permutation9 permutation4
    _ = injectiveMoment H node193 := by rfl

theorem canonical10177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10177 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw10177 = injectiveMoment H raw10177step0 := by
      have heq : raw10177step0 = raw10177.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10177).symm
    injectiveMoment H raw10177step0 = injectiveMoment H raw10177step1 := by
      have heq : raw10177step1 = -raw10177step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10177step0).symm
    injectiveMoment H raw10177step1 = injectiveMoment H raw10177step2 := by
      have heq : raw10177step2 = (fun i j => raw10177step1 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10177step1 permutation9 permutation4
    _ = injectiveMoment H node198 := by rfl

theorem canonical10179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10179 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw10179 = injectiveMoment H raw10179step0 := by
      have heq : raw10179step0 = raw10179.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10179).symm
    injectiveMoment H raw10179step0 = injectiveMoment H raw10179step1 := by
      have heq : raw10179step1 = (fun i j => raw10179step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10179step0 permutation30 permutation3
    _ = injectiveMoment H node193 := by rfl

theorem canonical10180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10180 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw10180 = injectiveMoment H raw10180step0 := by
      have heq : raw10180step0 = raw10180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10180).symm
    injectiveMoment H raw10180step0 = injectiveMoment H raw10180step1 := by
      have heq : raw10180step1 = (fun i j => raw10180step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10180step0 permutation30 permutation3
    _ = injectiveMoment H node198 := by rfl

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

theorem canonical1268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1268 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1268 = injectiveMoment H raw1268step0 := by
      have heq : raw1268step0 = raw1268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1268).symm
    injectiveMoment H raw1268step0 = injectiveMoment H raw1268step1 := by
      have heq : raw1268step1 = (fun i j => raw1268step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1268step0 permutation30 permutation26
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

theorem canonical1336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1336 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw1336 = injectiveMoment H raw1336step0 := by
      have heq : raw1336step0 = raw1336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1336).symm
    injectiveMoment H raw1336step0 = injectiveMoment H raw1336step1 := by
      have heq : raw1336step1 = -raw1336step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1336step0).symm
    injectiveMoment H raw1336step1 = injectiveMoment H raw1336step2 := by
      have heq : raw1336step2 = (fun i j => raw1336step1 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1336step1 permutation11 permutation6
    _ = injectiveMoment H node191 := by rfl

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

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2049 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw2049 = injectiveMoment H raw2049step0 := by
      have heq : raw2049step0 = raw2049.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2049).symm
    injectiveMoment H raw2049step0 = injectiveMoment H raw2049step1 := by
      have heq : raw2049step1 = (fun i j => raw2049step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2049step0 permutation32 permutation24
    _ = injectiveMoment H node1202 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2100 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw2100 = injectiveMoment H raw2100step0 := by
      have heq : raw2100step0 = raw2100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2100).symm
    injectiveMoment H raw2100step0 = injectiveMoment H raw2100step1 := by
      have heq : raw2100step1 = (fun i j => raw2100step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2100step0 permutation30 permutation32
    _ = injectiveMoment H node476 := by rfl

theorem canonical2103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2103 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw2103 = injectiveMoment H raw2103step0 := by
      have heq : raw2103step0 = raw2103.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2103).symm
    injectiveMoment H raw2103step0 = injectiveMoment H raw2103step1 := by
      have heq : raw2103step1 = (fun i j => raw2103step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2103step0 permutation32 permutation24
    _ = injectiveMoment H node1190 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2625 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2625 = injectiveMoment H raw2625step0 := by
      have heq : raw2625step0 = raw2625.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2625).symm
    injectiveMoment H raw2625step0 = injectiveMoment H raw2625step1 := by
      have heq : raw2625step1 = (fun i j => raw2625step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2625step0 permutation22 permutation6
    _ = injectiveMoment H node111 := by rfl

theorem canonical2637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2637 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw2637 = injectiveMoment H raw2637step0 := by
      have heq : raw2637step0 = raw2637.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2637).symm
    injectiveMoment H raw2637step0 = injectiveMoment H raw2637step1 := by
      have heq : raw2637step1 = -raw2637step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2637step0).symm
    injectiveMoment H raw2637step1 = injectiveMoment H raw2637step2 := by
      have heq : raw2637step2 = (fun i j => raw2637step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2637step1 permutation26 permutation4
    _ = injectiveMoment H node135 := by rfl

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

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
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

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound51 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node51 = Sparse.eval value51 (momentVector H) := by
  have heq : pivotMatrix51 = (fun u v => node51 (pivotPermutation51 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node51 = injectiveMoment H pivotMatrix51 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix51 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix51 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (0 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node51 + (injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value51, value10, value8, Sparse.eval] at hc ⊢
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

theorem sound54 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node54 = Sparse.eval value54 (momentVector H) := by
  have heq : pivotMatrix54 = (fun u v => node54 (pivotPermutation54 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node54 = injectiveMoment H pivotMatrix54 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix54 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix54 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix54 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix54 (0 : Fin 2) = raw7988 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7988 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix54 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix54 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node54 + (injectiveMoment H (mergeFirst pivotMatrix54 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix54 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value54, value2, value8, Sparse.eval] at hc ⊢
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

theorem sound58 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node58 = Sparse.eval value58 (momentVector H) := by
  have heq : pivotMatrix58 = (fun u v => node58 (pivotPermutation58 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node58 = injectiveMoment H pivotMatrix58 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix58 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix58 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node58 + (injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value58, value10, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node59 = Sparse.eval value59 (momentVector H) := by
  have heq : pivotMatrix59 = (fun u v => node59.transpose (pivotPermutation59 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node59 = injectiveMoment H pivotMatrix59 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix59 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (0 : Fin 2) = raw928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical928 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (1 : Fin 2) = raw5459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5459 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node59 + (injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value59, value8, value9, Sparse.eval] at hc ⊢
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

theorem sound111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node111 = Sparse.eval value111 (momentVector H) := by
  have hc : momentVector H 33 = injectiveMoment H node111 := rfl
  simp [value111, Sparse.eval, hc]

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

theorem sound135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node135 = Sparse.eval value135 (momentVector H) := by
  have hc : momentVector H 306 = injectiveMoment H node135 := rfl
  simp [value135, Sparse.eval, hc]

theorem sound149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node149 = Sparse.eval value149 (momentVector H) := by
  have heq : pivotMatrix149 = (fun u v => node149 (pivotPermutation149 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node149 = injectiveMoment H pivotMatrix149 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix149 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix149 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix149 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (0 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix149 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (1 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix149 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (2 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node149 + (injectiveMoment H (mergeFirst pivotMatrix149 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix149 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix149 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value149, value52, value59, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node152 = Sparse.eval value152 (momentVector H) := by
  have hc : momentVector H 308 = injectiveMoment H node152 := rfl
  simp [value152, Sparse.eval, hc]

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node184 = Sparse.eval value184 (momentVector H) := by
  have hc : momentVector H 51 = injectiveMoment H node184 := rfl
  simp [value184, Sparse.eval, hc]

theorem sound191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node191 = Sparse.eval value191 (momentVector H) := by
  have hc : momentVector H 721 = injectiveMoment H node191 := rfl
  simp [value191, Sparse.eval, hc]

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

theorem sound193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node193 = Sparse.eval value193 (momentVector H) := by
  have hc : momentVector H 723 = injectiveMoment H node193 := rfl
  simp [value193, Sparse.eval, hc]

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

theorem sound243 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node243 = Sparse.eval value243 (momentVector H) := by
  have heq : pivotMatrix243 = (fun u v => node243 (pivotPermutation243 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node243 = injectiveMoment H pivotMatrix243 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix243 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix243 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix243 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix243 (1 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (1 : Fin 3) = raw5540 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5540 hH).trans (sound51 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix243 (2 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (2 : Fin 3) = raw5554 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5554 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node243 + (injectiveMoment H (mergeFirst pivotMatrix243 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix243 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix243 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value243, value51, value52, value53, Sparse.eval] at hc ⊢
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

theorem sound272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node272 = Sparse.eval value272 (momentVector H) := by
  have heq : pivotMatrix272 = (fun u v => node272 (pivotPermutation272 u) v) := by apply Matrix.ext; unfold pivotMatrix272 node272 pivotPermutation272; decide +kernel
  have hmoment : injectiveMoment H node272 = injectiveMoment H pivotMatrix272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix272 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix272 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (1 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node272 + (injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value272, value57, value58, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node290 = Sparse.eval value290 (momentVector H) := by
  have heq : pivotMatrix290 = (fun u v => node290 (pivotPermutation290 u) v) := by apply Matrix.ext; unfold pivotMatrix290 node290 pivotPermutation290; decide +kernel
  have hmoment : injectiveMoment H node290 = injectiveMoment H pivotMatrix290 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix290 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix290 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix290 (0 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix290 (0 : Fin 3) = raw5552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix290 raw5552; decide +kernel
    rw [heq]
    exact (canonical5552 hH).trans (sound54 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix290 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix290 (1 : Fin 3) = raw7997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix290 raw7997; decide +kernel
    rw [heq]
    exact (canonical7997 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix290 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix290 (2 : Fin 3) = raw8007 := by apply Matrix.ext; unfold mergeFirst pivotMatrix290 raw8007; decide +kernel
    rw [heq]
    exact (canonical8007 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node290 + (injectiveMoment H (mergeFirst pivotMatrix290 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix290 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix290 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value290, value53, value54, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound292 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node292 = Sparse.eval value292 (momentVector H) := by
  have heq : pivotMatrix292 = (fun u v => node292 (pivotPermutation292 u) v) := by apply Matrix.ext; unfold pivotMatrix292 node292 pivotPermutation292; decide +kernel
  have hmoment : injectiveMoment H node292 = injectiveMoment H pivotMatrix292 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix292 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix292 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix292 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix292 (0 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix292 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix292 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix292 (1 : Fin 3) = raw8169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix292 raw8169; decide +kernel
    rw [heq]
    exact (canonical8169 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix292 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix292 (2 : Fin 3) = raw8217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix292 raw8217; decide +kernel
    rw [heq]
    exact (canonical8217 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node292 + (injectiveMoment H (mergeFirst pivotMatrix292 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix292 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix292 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value292, value10, value57, value58, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node688 = Sparse.eval value688 (momentVector H) := by
  have hc : momentVector H 764 = injectiveMoment H node688 := rfl
  simp [value688, Sparse.eval, hc]

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

theorem sound1007 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1007 = Sparse.eval value1007 (momentVector H) := by
  have heq : pivotMatrix1007 = (fun u v => node1007.transpose (pivotPermutation1007 u) v) := by apply Matrix.ext; unfold pivotMatrix1007 node1007 pivotPermutation1007; decide +kernel
  have hmoment : injectiveMoment H node1007 = injectiveMoment H pivotMatrix1007 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1007 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1007 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1007 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1007 (0 : Fin 3) = raw2625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1007 raw2625; decide +kernel
    rw [heq]
    exact (canonical2625 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1007 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1007 (1 : Fin 3) = raw6905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1007 raw6905; decide +kernel
    rw [heq]
    exact (canonical6905 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1007 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1007 (2 : Fin 3) = raw6934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1007 raw6934; decide +kernel
    rw [heq]
    exact (canonical6934 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1007 + (injectiveMoment H (mergeFirst pivotMatrix1007 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1007 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1007 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1007, value111, value181, value184, Sparse.eval] at hc ⊢
  linarith

theorem sound1014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1014 = Sparse.eval value1014 (momentVector H) := by
  have heq : pivotMatrix1014 = (fun u v => node1014.transpose (pivotPermutation1014 u) v) := by apply Matrix.ext; unfold pivotMatrix1014 node1014 pivotPermutation1014; decide +kernel
  have hmoment : injectiveMoment H node1014 = injectiveMoment H pivotMatrix1014 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1014 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1014 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1014 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1014 (0 : Fin 3) = raw2637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1014 raw2637; decide +kernel
    rw [heq]
    exact (canonical2637 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1014 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1014 (1 : Fin 3) = raw6909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1014 raw6909; decide +kernel
    rw [heq]
    exact (canonical6909 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1014 (2 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1014 (2 : Fin 3) = raw6937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1014 raw6937; decide +kernel
    rw [heq]
    exact (canonical6937 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1014 + (injectiveMoment H (mergeFirst pivotMatrix1014 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1014 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1014 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1014, value135, value149, value152, Sparse.eval] at hc ⊢
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

theorem sound1154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1154 = Sparse.eval value1154 (momentVector H) := by
  have heq : pivotMatrix1154 = (fun u v => node1154.transpose (pivotPermutation1154 u) v) := by apply Matrix.ext; unfold pivotMatrix1154 node1154 pivotPermutation1154; decide +kernel
  have hmoment : injectiveMoment H node1154 = injectiveMoment H pivotMatrix1154 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1154 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1154 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1154 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1154 (0 : Fin 3) = raw1336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1154 raw1336; decide +kernel
    rw [heq]
    exact (canonical1336 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1154 (1 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1154 (1 : Fin 3) = raw5996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1154 raw5996; decide +kernel
    rw [heq]
    exact (canonical5996 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1154 (2 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1154 (2 : Fin 3) = raw5997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1154 raw5997; decide +kernel
    rw [heq]
    exact (canonical5997 hH).trans (sound84 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1154 + (injectiveMoment H (mergeFirst pivotMatrix1154 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1154 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1154 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1154, value191, value243, value84, Sparse.eval] at hc ⊢
  linarith

theorem sound1178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1178 = Sparse.eval value1178 (momentVector H) := by
  have heq : pivotMatrix1178 = (fun u v => node1178 (pivotPermutation1178 u) v) := by apply Matrix.ext; unfold pivotMatrix1178 node1178 pivotPermutation1178; decide +kernel
  have hmoment : injectiveMoment H node1178 = injectiveMoment H pivotMatrix1178 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1178 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1178 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1178 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (0 : Fin 3) = raw8286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw8286; decide +kernel
    rw [heq]
    exact (canonical8286 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1178 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (1 : Fin 3) = raw7041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw7041; decide +kernel
    rw [heq]
    exact (canonical7041 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1178 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (2 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1178 + (injectiveMoment H (mergeFirst pivotMatrix1178 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1178 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1178 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1178, value149, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound1190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1190 = Sparse.eval value1190 (momentVector H) := by
  have heq : pivotMatrix1190 = (fun u v => node1190.transpose (pivotPermutation1190 u) v) := by apply Matrix.ext; unfold pivotMatrix1190 node1190 pivotPermutation1190; decide +kernel
  have hmoment : injectiveMoment H node1190 = injectiveMoment H pivotMatrix1190 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1190 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1190 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1190 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (0 : Fin 3) = raw5813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw5813; decide +kernel
    rw [heq]
    exact (canonical5813 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1190 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (1 : Fin 3) = raw8227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw8227; decide +kernel
    rw [heq]
    exact (canonical8227 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1190 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (2 : Fin 3) = raw8235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw8235; decide +kernel
    rw [heq]
    exact (canonical8235 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1190 + (injectiveMoment H (mergeFirst pivotMatrix1190 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1190 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1190 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1190, value111, value198, value203, Sparse.eval] at hc ⊢
  linarith

theorem sound1202 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1202 = Sparse.eval value1202 (momentVector H) := by
  have heq : pivotMatrix1202 = (fun u v => node1202 (pivotPermutation1202 u) v) := by apply Matrix.ext; unfold pivotMatrix1202 node1202 pivotPermutation1202; decide +kernel
  have hmoment : injectiveMoment H node1202 = injectiveMoment H pivotMatrix1202 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1202 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1202 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1202 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (0 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1202 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (1 : Fin 3) = raw7101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw7101; decide +kernel
    rw [heq]
    exact (canonical7101 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1202 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (2 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1202 + (injectiveMoment H (mergeFirst pivotMatrix1202 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1202 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1202 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1202, value271, value272, value56, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound9
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node576 = Sparse.eval value576 (momentVector H) := by
  have hc : momentVector H 498 = injectiveMoment H node576 := rfl
  simp [value576, Sparse.eval, hc]

theorem sound584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node584 = Sparse.eval value584 (momentVector H) := by
  have hc : momentVector H 507 = injectiveMoment H node584 := rfl
  simp [value584, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound21
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1373 = Sparse.eval value1373 (momentVector H) := by
  have heq : pivotMatrix1373 = (fun u v => node1373.transpose (pivotPermutation1373 u) v) := by apply Matrix.ext; unfold pivotMatrix1373 node1373 pivotPermutation1373; decide +kernel
  have hmoment : injectiveMoment H node1373 = injectiveMoment H pivotMatrix1373 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1373 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1373 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1373 (0 : Fin 3)) =
      Sparse.eval value290 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1373 (0 : Fin 3) = raw10139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1373 raw10139; decide +kernel
    rw [heq]
    exact (canonical10139 hH).trans (sound290 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1373 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1373 (1 : Fin 3) = raw10176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1373 raw10176; decide +kernel
    rw [heq]
    exact (canonical10176 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1373 (2 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1373 (2 : Fin 3) = raw10179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1373 raw10179; decide +kernel
    rw [heq]
    exact (canonical10179 hH).trans (sound193 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1373 + (injectiveMoment H (mergeFirst pivotMatrix1373 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1373 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1373 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1373, value193, value290, Sparse.eval] at hc ⊢
  linarith

theorem sound1374 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1374 = Sparse.eval value1374 (momentVector H) := by
  have heq : pivotMatrix1374 = (fun u v => node1374.transpose (pivotPermutation1374 u) v) := by apply Matrix.ext; unfold pivotMatrix1374 node1374 pivotPermutation1374; decide +kernel
  have hmoment : injectiveMoment H node1374 = injectiveMoment H pivotMatrix1374 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1374 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1374 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1374 (0 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1374 (0 : Fin 3) = raw10141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1374 raw10141; decide +kernel
    rw [heq]
    exact (canonical10141 hH).trans (sound292 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1374 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1374 (1 : Fin 3) = raw10177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1374 raw10177; decide +kernel
    rw [heq]
    exact (canonical10177 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1374 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1374 (2 : Fin 3) = raw10180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1374 raw10180; decide +kernel
    rw [heq]
    exact (canonical10180 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1374 + (injectiveMoment H (mergeFirst pivotMatrix1374 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1374 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1374 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1374, value198, value292, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound7
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node453 = Sparse.eval value453 (momentVector H) := by
  have hc : momentVector H 315 = injectiveMoment H node453 := rfl
  simp [value453, Sparse.eval, hc]

theorem sound476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node476 = Sparse.eval value476 (momentVector H) := by
  have hc : momentVector H 39 = injectiveMoment H node476 := rfl
  simp [value476, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound25
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1642 = Sparse.eval value1642 (momentVector H) := by
  have heq : pivotMatrix1642 = (fun u v => node1642 (pivotPermutation1642 u) v) := by apply Matrix.ext; unfold pivotMatrix1642 node1642 pivotPermutation1642; decide +kernel
  have hmoment : injectiveMoment H node1642 = injectiveMoment H pivotMatrix1642 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1642 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1642 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1642 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (0 : Fin 4) = raw1268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw1268; decide +kernel
    rw [heq]
    exact (canonical1268 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1642 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (1 : Fin 4) = raw2049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw2049; decide +kernel
    rw [heq]
    exact (canonical2049 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1642 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (2 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1642 (3 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (3 : Fin 4) = raw2103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw2103; decide +kernel
    rw [heq]
    exact (canonical2103 hH).trans (sound1190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1642 + (injectiveMoment H (mergeFirst pivotMatrix1642 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1642 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1642 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1642 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1642, value1190, value1202, value476, value804, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound36
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2348 = Sparse.eval value2348 (momentVector H) := by
  have heq : pivotMatrix2348 = (fun u v => node2348 (pivotPermutation2348 u) v) := by apply Matrix.ext; unfold pivotMatrix2348 node2348 pivotPermutation2348; decide +kernel
  have hmoment : injectiveMoment H node2348 = injectiveMoment H pivotMatrix2348 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2348 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2348 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2348 (0 : Fin 4)) =
      Sparse.eval value1014 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (0 : Fin 4) = raw5243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5243; decide +kernel
    rw [heq]
    exact (canonical5243 hH).trans (sound1014 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2348 (1 : Fin 4)) =
      Sparse.eval value1154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (1 : Fin 4) = raw5305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5305; decide +kernel
    rw [heq]
    exact (canonical5305 hH).trans (sound1154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2348 (2 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (2 : Fin 4) = raw5308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5308; decide +kernel
    rw [heq]
    exact (canonical5308 hH).trans (sound453 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2348 (3 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (3 : Fin 4) = raw5309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5309; decide +kernel
    rw [heq]
    exact (canonical5309 hH).trans (sound1007 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2348 + (injectiveMoment H (mergeFirst pivotMatrix2348 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2348 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2348 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2348 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2348, value1007, value1014, value1154, value453, Sparse.eval] at hc ⊢
  linarith

theorem sound2364 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2364 = Sparse.eval value2364 (momentVector H) := by
  have heq : pivotMatrix2364 = (fun u v => node2364 (pivotPermutation2364 u) v) := by apply Matrix.ext; unfold pivotMatrix2364 node2364 pivotPermutation2364; decide +kernel
  have hmoment : injectiveMoment H node2364 = injectiveMoment H pivotMatrix2364 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2364 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2364 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2364 (0 : Fin 4)) =
      Sparse.eval value1154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (0 : Fin 4) = raw5448 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5448; decide +kernel
    rw [heq]
    exact (canonical5448 hH).trans (sound1154 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2364 (1 : Fin 4)) =
      Sparse.eval value1374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (1 : Fin 4) = raw5403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5403; decide +kernel
    rw [heq]
    exact (canonical5403 hH).trans (sound1374 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2364 (2 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (2 : Fin 4) = raw5397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5397; decide +kernel
    rw [heq]
    exact (canonical5397 hH).trans (sound688 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2364 (3 : Fin 4)) =
      Sparse.eval value1373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (3 : Fin 4) = raw5396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5396; decide +kernel
    rw [heq]
    exact (canonical5396 hH).trans (sound1373 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2364 + (injectiveMoment H (mergeFirst pivotMatrix2364 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2364 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2364 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2364 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2364, value1154, value1373, value1374, value688, Sparse.eval] at hc ⊢
  linarith

theorem sound2365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2365 = Sparse.eval value2365 (momentVector H) := by
  have heq : pivotMatrix2365 = (fun u v => node2365 (pivotPermutation2365 u) v) := by apply Matrix.ext; unfold pivotMatrix2365 node2365 pivotPermutation2365; decide +kernel
  have hmoment : injectiveMoment H node2365 = injectiveMoment H pivotMatrix2365 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2365 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2365 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2365 (0 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (0 : Fin 4) = raw5449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5449; decide +kernel
    rw [heq]
    exact (canonical5449 hH).trans (sound453 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2365 (1 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (1 : Fin 4) = raw5404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5404; decide +kernel
    rw [heq]
    exact (canonical5404 hH).trans (sound476 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2365 (2 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (2 : Fin 4) = raw5398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5398; decide +kernel
    rw [heq]
    exact (canonical5398 hH).trans (sound584 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2365 (3 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (3 : Fin 4) = raw5397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5397; decide +kernel
    rw [heq]
    exact (canonical5397 hH).trans (sound688 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2365 + (injectiveMoment H (mergeFirst pivotMatrix2365 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2365 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2365 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2365 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2365, value453, value476, value584, value688, Sparse.eval] at hc ⊢
  linarith

theorem sound2367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2367 = Sparse.eval value2367 (momentVector H) := by
  have heq : pivotMatrix2367 = (fun u v => node2367 (pivotPermutation2367 u) v) := by apply Matrix.ext; unfold pivotMatrix2367 node2367 pivotPermutation2367; decide +kernel
  have hmoment : injectiveMoment H node2367 = injectiveMoment H pivotMatrix2367 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2367 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2367 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2367 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (0 : Fin 4) = raw7896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw7896; decide +kernel
    rw [heq]
    exact (canonical7896 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2367 (1 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (1 : Fin 4) = raw5443 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw5443; decide +kernel
    rw [heq]
    exact (canonical5443 hH).trans (sound394 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2367 (2 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (2 : Fin 4) = raw5398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw5398; decide +kernel
    rw [heq]
    exact (canonical5398 hH).trans (sound584 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2367 (3 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (3 : Fin 4) = raw5395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw5395; decide +kernel
    rw [heq]
    exact (canonical5395 hH).trans (sound576 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2367 + (injectiveMoment H (mergeFirst pivotMatrix2367 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2367 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2367 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2367 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2367, value1178, value394, value576, value584, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound51
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3324_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3324 = Sparse.eval value3324 (momentVector H) := by
  have heq : pivotMatrix3324 = (fun u v => node3324 (pivotPermutation3324 u) v) := by apply Matrix.ext; unfold pivotMatrix3324 node3324 pivotPermutation3324; decide +kernel
  have hmoment : injectiveMoment H node3324 = injectiveMoment H pivotMatrix3324 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3324 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3324 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3324 (0 : Fin 5)) =
      Sparse.eval value2348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3324 (0 : Fin 5) = raw5446 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3324 raw5446; decide +kernel
    rw [heq]
    exact (canonical5446 hH).trans (sound2348 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3324 (1 : Fin 5)) =
      Sparse.eval value1642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3324 (1 : Fin 5) = raw5401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3324 raw5401; decide +kernel
    rw [heq]
    exact (canonical5401 hH).trans (sound1642 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3324 (2 : Fin 5)) =
      Sparse.eval value2367 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3324 (2 : Fin 5) = raw5393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3324 raw5393; decide +kernel
    rw [heq]
    exact (canonical5393 hH).trans (sound2367 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3324 (3 : Fin 5)) =
      Sparse.eval value2365 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3324 (3 : Fin 5) = raw5390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3324 raw5390; decide +kernel
    rw [heq]
    exact (canonical5390 hH).trans (sound2365 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3324 (4 : Fin 5)) =
      Sparse.eval value2364 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3324 (4 : Fin 5) = raw5389 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3324 raw5389; decide +kernel
    rw [heq]
    exact (canonical5389 hH).trans (sound2364 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3324 + (injectiveMoment H (mergeFirst pivotMatrix3324 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3324 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3324 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3324 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3324 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3324, value1642, value2348, value2364, value2365, value2367, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3324_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3324_e_oai
