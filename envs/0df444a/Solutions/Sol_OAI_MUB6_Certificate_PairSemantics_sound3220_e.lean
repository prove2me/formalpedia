-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3220_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:15:11.475088+00:00
-- url     : https://prove2.me/submissions/efa5ae15-8692-4705-b206-b52f10c73d04

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3242 = injectiveMoment H node598 := by
  rfl

theorem canonical3244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3244 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw3244 = injectiveMoment H raw3244step0 := by
      have heq : raw3244step0 = -raw3244 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3244).symm
    injectiveMoment H raw3244step0 = injectiveMoment H raw3244step1 := by
      have heq : raw3244step1 = (fun i j => raw3244step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3244step0 permutation19 permutation17
    _ = injectiveMoment H node1081 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3270 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw3270 = injectiveMoment H raw3270step0 := by
      have heq : raw3270step0 = raw3270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3270).symm
    injectiveMoment H raw3270step0 = injectiveMoment H raw3270step1 := by
      have heq : raw3270step1 = -raw3270step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3270step0).symm
    injectiveMoment H raw3270step1 = injectiveMoment H raw3270step2 := by
      have heq : raw3270step2 = (fun i j => raw3270step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3270step1 permutation10 permutation30
    _ = injectiveMoment H node1235 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3417 = injectiveMoment H node602 := by
  calc
    injectiveMoment H raw3417 = injectiveMoment H raw3417step0 := by
      have heq : raw3417step0 = -raw3417 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3417).symm
    injectiveMoment H raw3417step0 = injectiveMoment H raw3417step1 := by
      have heq : raw3417step1 = (fun i j => raw3417step0 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3417step0 permutation22 permutation16
    _ = injectiveMoment H node602 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3496 = injectiveMoment H node1322 := by
  calc
    injectiveMoment H raw3496 = injectiveMoment H raw3496step0 := by
      have heq : raw3496step0 = -raw3496 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3496).symm
    injectiveMoment H raw3496step0 = injectiveMoment H raw3496step1 := by
      have heq : raw3496step1 = (fun i j => raw3496step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3496step0 permutation23 permutation15
    _ = injectiveMoment H node1322 := by rfl

theorem canonical3504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3504 = injectiveMoment H node591 := by
  calc
    injectiveMoment H raw3504 = injectiveMoment H raw3504step0 := by
      have heq : raw3504step0 = -raw3504 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3504).symm
    injectiveMoment H raw3504step0 = injectiveMoment H raw3504step1 := by
      have heq : raw3504step1 = (fun i j => raw3504step0 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3504step0 permutation23 permutation16
    _ = injectiveMoment H node591 := by rfl

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4195 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4195 = injectiveMoment H raw4195step0 := by
      have heq : raw4195step0 = raw4195.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4195).symm
    injectiveMoment H raw4195step0 = injectiveMoment H raw4195step1 := by
      have heq : raw4195step1 = -raw4195step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4195step0).symm
    injectiveMoment H raw4195step1 = injectiveMoment H raw4195step2 := by
      have heq : raw4195step2 = (fun i j => raw4195step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4195step1 permutation26 permutation4
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4226 = injectiveMoment H node2146 := by
  rfl

theorem canonical4227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4227 = injectiveMoment H node2760 := by
  calc
    injectiveMoment H raw4227 = injectiveMoment H raw4227step0 := by
      have heq : raw4227step0 = -raw4227 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4227).symm
    injectiveMoment H raw4227step0 = injectiveMoment H raw4227step1 := by
      have heq : raw4227step1 = (fun i j => raw4227step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4227step0 permutation100 permutation15
    _ = injectiveMoment H node2760 := by rfl

theorem canonical4228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4228 = injectiveMoment H node2008 := by
  calc
    injectiveMoment H raw4228 = injectiveMoment H raw4228step0 := by
      have heq : raw4228step0 = -raw4228 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4228).symm
    injectiveMoment H raw4228step0 = injectiveMoment H raw4228step1 := by
      have heq : raw4228step1 = (fun i j => raw4228step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4228step0 permutation100 permutation15
    _ = injectiveMoment H node2008 := by rfl

theorem canonical4229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4229 = injectiveMoment H node480 := by
  calc
    injectiveMoment H raw4229 = injectiveMoment H raw4229step0 := by
      have heq : raw4229step0 = -raw4229 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4229).symm
    injectiveMoment H raw4229step0 = injectiveMoment H raw4229step1 := by
      have heq : raw4229step1 = (fun i j => raw4229step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4229step0 permutation29 permutation15
    _ = injectiveMoment H node480 := by rfl

theorem canonical4230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4230 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw4230 = injectiveMoment H raw4230step0 := by
      have heq : raw4230step0 = -raw4230 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4230).symm
    injectiveMoment H raw4230step0 = injectiveMoment H raw4230step1 := by
      have heq : raw4230step1 = (fun i j => raw4230step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4230step0 permutation29 permutation15
    _ = injectiveMoment H node1056 := by rfl

theorem canonical4231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4231 = injectiveMoment H node1982 := by
  calc
    injectiveMoment H raw4231 = injectiveMoment H raw4231step0 := by
      have heq : raw4231step0 = (fun i j => raw4231 (permutation39 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4231 permutation39 permutation10
    _ = injectiveMoment H node1982 := by rfl

theorem canonical4232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4232 = injectiveMoment H node598 := by
  calc
    injectiveMoment H raw4232 = injectiveMoment H raw4232step0 := by
      have heq : raw4232step0 = (fun i j => raw4232 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4232 permutation9 permutation10
    _ = injectiveMoment H node598 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4427 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw4427 = injectiveMoment H raw4427step0 := by
      have heq : raw4427step0 = raw4427.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4427).symm
    injectiveMoment H raw4427step0 = injectiveMoment H raw4427step1 := by
      have heq : raw4427step1 = -raw4427step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4427step0).symm
    injectiveMoment H raw4427step1 = injectiveMoment H raw4427step2 := by
      have heq : raw4427step2 = (fun i j => raw4427step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4427step1 permutation10 permutation30
    _ = injectiveMoment H node1248 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4501 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw4501 = injectiveMoment H raw4501step0 := by
      have heq : raw4501step0 = raw4501.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4501).symm
    injectiveMoment H raw4501step0 = injectiveMoment H raw4501step1 := by
      have heq : raw4501step1 = (fun i j => raw4501step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4501step0 permutation21 permutation19
    _ = injectiveMoment H node593 := by rfl

theorem canonical4504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4504 = injectiveMoment H node1317 := by
  calc
    injectiveMoment H raw4504 = injectiveMoment H raw4504step0 := by
      have heq : raw4504step0 = raw4504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4504).symm
    injectiveMoment H raw4504step0 = injectiveMoment H raw4504step1 := by
      have heq : raw4504step1 = -raw4504step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4504step0).symm
    injectiveMoment H raw4504step1 = injectiveMoment H raw4504step2 := by
      have heq : raw4504step2 = (fun i j => raw4504step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4504step1 permutation9 permutation29
    _ = injectiveMoment H node1317 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4609 = injectiveMoment H node1310 := by
  calc
    injectiveMoment H raw4609 = injectiveMoment H raw4609step0 := by
      have heq : raw4609step0 = raw4609.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4609).symm
    injectiveMoment H raw4609step0 = injectiveMoment H raw4609step1 := by
      have heq : raw4609step1 = -raw4609step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4609step0).symm
    injectiveMoment H raw4609step1 = injectiveMoment H raw4609step2 := by
      have heq : raw4609step2 = (fun i j => raw4609step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4609step1 permutation9 permutation29
    _ = injectiveMoment H node1310 := by rfl

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

theorem canonical5094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5094 = injectiveMoment H node2216 := by
  calc
    injectiveMoment H raw5094 = injectiveMoment H raw5094step0 := by
      have heq : raw5094step0 = (fun i j => raw5094 (permutation114 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5094 permutation114 permutation15
    _ = injectiveMoment H node2216 := by rfl

theorem canonical5095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5095 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw5095 = injectiveMoment H raw5095step0 := by
      have heq : raw5095step0 = raw5095.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5095).symm
    injectiveMoment H raw5095step0 = injectiveMoment H raw5095step1 := by
      have heq : raw5095step1 = (fun i j => raw5095step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5095step0 permutation23 permutation20
    _ = injectiveMoment H node593 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5329 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw5329 = injectiveMoment H raw5329step0 := by
      have heq : raw5329step0 = raw5329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5329).symm
    injectiveMoment H raw5329step0 = injectiveMoment H raw5329step1 := by
      have heq : raw5329step1 = -raw5329step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5329step0).symm
    injectiveMoment H raw5329step1 = injectiveMoment H raw5329step2 := by
      have heq : raw5329step2 = (fun i j => raw5329step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5329step1 permutation9 permutation29
    _ = injectiveMoment H node1315 := by rfl

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

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

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

theorem canonical5819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5819 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5819 = injectiveMoment H raw5819step0 := by
      have heq : raw5819step0 = raw5819.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5819).symm
    injectiveMoment H raw5819step0 = injectiveMoment H raw5819step1 := by
      have heq : raw5819step1 = (fun i j => raw5819step0 (permutation24 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5819step0 permutation24 permutation8
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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6506 = injectiveMoment H node1056 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6552 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6552 = injectiveMoment H raw6552step0 := by
      have heq : raw6552step0 = raw6552.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6552).symm
    injectiveMoment H raw6552step0 = injectiveMoment H raw6552step1 := by
      have heq : raw6552step1 = -raw6552step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6552step0).symm
    injectiveMoment H raw6552step1 = injectiveMoment H raw6552step2 := by
      have heq : raw6552step2 = (fun i j => raw6552step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6552step1 permutation31 permutation4
    _ = injectiveMoment H node185 := by rfl

theorem canonical6559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6559 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6559 = injectiveMoment H raw6559step0 := by
      have heq : raw6559step0 = raw6559.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6559).symm
    injectiveMoment H raw6559step0 = injectiveMoment H raw6559step1 := by
      have heq : raw6559step1 = -raw6559step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6559step0).symm
    injectiveMoment H raw6559step1 = injectiveMoment H raw6559step2 := by
      have heq : raw6559step2 = (fun i j => raw6559step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6559step1 permutation31 permutation4
    _ = injectiveMoment H node181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6560 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6560 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw6560 = injectiveMoment H raw6560step0 := by
      have heq : raw6560step0 = raw6560.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6560).symm
    injectiveMoment H raw6560step0 = injectiveMoment H raw6560step1 := by
      have heq : raw6560step1 = -raw6560step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6560step0).symm
    injectiveMoment H raw6560step1 = injectiveMoment H raw6560step2 := by
      have heq : raw6560step2 = (fun i j => raw6560step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6560step1 permutation31 permutation4
    _ = injectiveMoment H node153 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6789 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw6789 = injectiveMoment H raw6789step0 := by
      have heq : raw6789step0 = -raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6789).symm
    injectiveMoment H raw6789step0 = injectiveMoment H raw6789step1 := by
      have heq : raw6789step1 = (fun i j => raw6789step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6789step0 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical6880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6880 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw6880 = injectiveMoment H raw6880step0 := by
      have heq : raw6880step0 = (fun i j => raw6880 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6880 permutation4 permutation3
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical6908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6908 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6908 = injectiveMoment H raw6908step0 := by
      have heq : raw6908step0 = raw6908.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6908).symm
    injectiveMoment H raw6908step0 = injectiveMoment H raw6908step1 := by
      have heq : raw6908step1 = -raw6908step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6908step0).symm
    injectiveMoment H raw6908step1 = injectiveMoment H raw6908step2 := by
      have heq : raw6908step2 = (fun i j => raw6908step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6908step1 permutation26 permutation3
    _ = injectiveMoment H node184 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6950 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6950 = injectiveMoment H raw6950step0 := by
      have heq : raw6950step0 = raw6950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6950).symm
    injectiveMoment H raw6950step0 = injectiveMoment H raw6950step1 := by
      have heq : raw6950step1 = -raw6950step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6950step0).symm
    injectiveMoment H raw6950step1 = injectiveMoment H raw6950step2 := by
      have heq : raw6950step2 = (fun i j => raw6950step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6950step1 permutation25 permutation3
    _ = injectiveMoment H node184 := by rfl

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

theorem canonical7245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7245 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7245 = injectiveMoment H raw7245step0 := by
      have heq : raw7245step0 = raw7245.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7245).symm
    injectiveMoment H raw7245step0 = injectiveMoment H raw7245step1 := by
      have heq : raw7245step1 = -raw7245step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7245step0).symm
    injectiveMoment H raw7245step1 = injectiveMoment H raw7245step2 := by
      have heq : raw7245step2 = (fun i j => raw7245step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7245step1 permutation29 permutation4
    _ = injectiveMoment H node181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7356 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7356 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7356 = injectiveMoment H raw7356step0 := by
      have heq : raw7356step0 = raw7356.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7356).symm
    injectiveMoment H raw7356step0 = injectiveMoment H raw7356step1 := by
      have heq : raw7356step1 = -raw7356step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7356step0).symm
    injectiveMoment H raw7356step1 = injectiveMoment H raw7356step2 := by
      have heq : raw7356step2 = (fun i j => raw7356step1 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7356step1 permutation30 permutation4
    _ = injectiveMoment H node272 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7512 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7512 = injectiveMoment H raw7512step0 := by
      have heq : raw7512step0 = raw7512.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7512).symm
    injectiveMoment H raw7512step0 = injectiveMoment H raw7512step1 := by
      have heq : raw7512step1 = -raw7512step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7512step0).symm
    injectiveMoment H raw7512step1 = injectiveMoment H raw7512step2 := by
      have heq : raw7512step2 = (fun i j => raw7512step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7512step1 permutation24 permutation3
    _ = injectiveMoment H node280 := by rfl

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

theorem canonical7536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7536 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7536 = injectiveMoment H raw7536step0 := by
      have heq : raw7536step0 = raw7536.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7536).symm
    injectiveMoment H raw7536step0 = injectiveMoment H raw7536step1 := by
      have heq : raw7536step1 = -raw7536step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7536step0).symm
    injectiveMoment H raw7536step1 = injectiveMoment H raw7536step2 := by
      have heq : raw7536step2 = (fun i j => raw7536step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7536step1 permutation23 permutation4
    _ = injectiveMoment H node184 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7589 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7589 = injectiveMoment H raw7589step0 := by
      have heq : raw7589step0 = raw7589.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7589).symm
    injectiveMoment H raw7589step0 = injectiveMoment H raw7589step1 := by
      have heq : raw7589step1 = -raw7589step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7589step0).symm
    injectiveMoment H raw7589step1 = injectiveMoment H raw7589step2 := by
      have heq : raw7589step2 = (fun i j => raw7589step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7589step1 permutation23 permutation4
    _ = injectiveMoment H node185 := by rfl

theorem canonical7591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7591 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw7591 = injectiveMoment H raw7591step0 := by
      have heq : raw7591step0 = raw7591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7591).symm
    injectiveMoment H raw7591step0 = injectiveMoment H raw7591step1 := by
      have heq : raw7591step1 = (fun i j => raw7591step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7591step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

theorem canonical7592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7592 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw7592 = injectiveMoment H raw7592step0 := by
      have heq : raw7592step0 = raw7592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7592).symm
    injectiveMoment H raw7592step0 = injectiveMoment H raw7592step1 := by
      have heq : raw7592step1 = -raw7592step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7592step0).symm
    injectiveMoment H raw7592step1 = injectiveMoment H raw7592step2 := by
      have heq : raw7592step2 = (fun i j => raw7592step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7592step1 permutation23 permutation3
    _ = injectiveMoment H node166 := by rfl

theorem canonical7606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7606 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7606 = injectiveMoment H raw7606step0 := by
      have heq : raw7606step0 = raw7606.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7606).symm
    injectiveMoment H raw7606step0 = injectiveMoment H raw7606step1 := by
      have heq : raw7606step1 = -raw7606step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7606step0).symm
    injectiveMoment H raw7606step1 = injectiveMoment H raw7606step2 := by
      have heq : raw7606step2 = (fun i j => raw7606step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7606step1 permutation23 permutation3
    _ = injectiveMoment H node184 := by rfl

theorem canonical7608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7608 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw7608 = injectiveMoment H raw7608step0 := by
      have heq : raw7608step0 = raw7608.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7608).symm
    injectiveMoment H raw7608step0 = injectiveMoment H raw7608step1 := by
      have heq : raw7608step1 = -raw7608step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7608step0).symm
    injectiveMoment H raw7608step1 = injectiveMoment H raw7608step2 := by
      have heq : raw7608step2 = (fun i j => raw7608step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7608step1 permutation23 permutation3
    _ = injectiveMoment H node212 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8236 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw8236 = injectiveMoment H raw8236step0 := by
      have heq : raw8236step0 = raw8236.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8236).symm
    injectiveMoment H raw8236step0 = injectiveMoment H raw8236step1 := by
      have heq : raw8236step1 = -raw8236step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8236step0).symm
    injectiveMoment H raw8236step1 = injectiveMoment H raw8236step2 := by
      have heq : raw8236step2 = (fun i j => raw8236step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8236step1 permutation25 permutation3
    _ = injectiveMoment H node177 := by rfl

theorem canonical8246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8246 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw8246 = injectiveMoment H raw8246step0 := by
      have heq : raw8246step0 = raw8246.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8246).symm
    injectiveMoment H raw8246step0 = injectiveMoment H raw8246step1 := by
      have heq : raw8246step1 = -raw8246step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8246step0).symm
    injectiveMoment H raw8246step1 = injectiveMoment H raw8246step2 := by
      have heq : raw8246step2 = (fun i j => raw8246step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8246step1 permutation22 permutation3
    _ = injectiveMoment H node177 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8366 = injectiveMoment H node1081 := by
  calc
    injectiveMoment H raw8366 = injectiveMoment H raw8366step0 := by
      have heq : raw8366step0 = (fun i j => raw8366 (permutation15 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8366 permutation15 permutation13
    _ = injectiveMoment H node1081 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8487 = injectiveMoment H node1083 := by
  calc
    injectiveMoment H raw8487 = injectiveMoment H raw8487step0 := by
      have heq : raw8487step0 = raw8487.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8487).symm
    injectiveMoment H raw8487step0 = injectiveMoment H raw8487step1 := by
      have heq : raw8487step1 = (fun i j => raw8487step0 (permutation15 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8487step0 permutation15 permutation13
    _ = injectiveMoment H node1083 := by rfl

theorem canonical8496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8496 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8496 = injectiveMoment H raw8496step0 := by
      have heq : raw8496step0 = -raw8496 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8496).symm
    injectiveMoment H raw8496step0 = injectiveMoment H raw8496step1 := by
      have hz : ∀ i, raw8496step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8496step1 = (fun i j => raw8496step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8496step0 permutation9 hz
    injectiveMoment H raw8496step1 = injectiveMoment H raw8496step2 := by
      have heq : raw8496step2 = (fun i j => raw8496step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8496step1 permutation23 permutation4
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8560 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8560 = injectiveMoment H raw8560step0 := by
      have hz : ∀ i, raw8560 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8560step0 = (fun i j => raw8560 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8560 permutation3 hz
    injectiveMoment H raw8560step0 = injectiveMoment H raw8560step1 := by
      have heq : raw8560step1 = (fun i j => raw8560step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8560step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8897 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw8897 = injectiveMoment H raw8897step0 := by
      have heq : raw8897step0 = raw8897.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8897).symm
    injectiveMoment H raw8897step0 = injectiveMoment H raw8897step1 := by
      have heq : raw8897step1 = -raw8897step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8897step0).symm
    injectiveMoment H raw8897step1 = injectiveMoment H raw8897step2 := by
      have heq : raw8897step2 = (fun i j => raw8897step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8897step1 permutation21 permutation3
    _ = injectiveMoment H node184 := by rfl

theorem canonical8910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8910 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw8910 = injectiveMoment H raw8910step0 := by
      have heq : raw8910step0 = raw8910.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8910).symm
    injectiveMoment H raw8910step0 = injectiveMoment H raw8910step1 := by
      have heq : raw8910step1 = -raw8910step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8910step0).symm
    injectiveMoment H raw8910step1 = injectiveMoment H raw8910step2 := by
      have heq : raw8910step2 = (fun i j => raw8910step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8910step1 permutation21 permutation3
    _ = injectiveMoment H node180 := by rfl

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

theorem canonical8928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8928 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw8928 = injectiveMoment H raw8928step0 := by
      have heq : raw8928step0 = raw8928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8928).symm
    injectiveMoment H raw8928step0 = injectiveMoment H raw8928step1 := by
      have heq : raw8928step1 = -raw8928step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8928step0).symm
    injectiveMoment H raw8928step1 = injectiveMoment H raw8928step2 := by
      have heq : raw8928step2 = (fun i j => raw8928step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8928step1 permutation21 permutation3
    _ = injectiveMoment H node175 := by rfl

theorem canonical8934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8934 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw8934 = injectiveMoment H raw8934step0 := by
      have heq : raw8934step0 = raw8934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8934).symm
    injectiveMoment H raw8934step0 = injectiveMoment H raw8934step1 := by
      have heq : raw8934step1 = -raw8934step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8934step0).symm
    injectiveMoment H raw8934step1 = injectiveMoment H raw8934step2 := by
      have heq : raw8934step2 = (fun i j => raw8934step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8934step1 permutation21 permutation3
    _ = injectiveMoment H node167 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9987 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9987 = injectiveMoment H raw9987step0 := by
      have heq : raw9987step0 = raw9987.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9987).symm
    injectiveMoment H raw9987step0 = injectiveMoment H raw9987step1 := by
      have heq : raw9987step1 = -raw9987step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9987step0).symm
    injectiveMoment H raw9987step1 = injectiveMoment H raw9987step2 := by
      have heq : raw9987step2 = (fun i j => raw9987step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9987step1 permutation21 permutation3
    _ = injectiveMoment H node169 := by rfl

theorem canonical9990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9990 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw9990 = injectiveMoment H raw9990step0 := by
      have heq : raw9990step0 = raw9990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9990).symm
    injectiveMoment H raw9990step0 = injectiveMoment H raw9990step1 := by
      have heq : raw9990step1 = (fun i j => raw9990step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9990step0 permutation29 permutation3
    _ = injectiveMoment H node197 := by rfl

theorem canonical9991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9991 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw9991 = injectiveMoment H raw9991step0 := by
      have heq : raw9991step0 = raw9991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9991).symm
    injectiveMoment H raw9991step0 = injectiveMoment H raw9991step1 := by
      have heq : raw9991step1 = (fun i j => raw9991step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9991step0 permutation29 permutation3
    _ = injectiveMoment H node162 := by rfl

theorem canonical9993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9993 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw9993 = injectiveMoment H raw9993step0 := by
      have heq : raw9993step0 = raw9993.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9993).symm
    injectiveMoment H raw9993step0 = injectiveMoment H raw9993step1 := by
      have heq : raw9993step1 = (fun i j => raw9993step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9993step0 permutation29 permutation3
    _ = injectiveMoment H node163 := by rfl

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

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1965 = injectiveMoment H node480 := by
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

theorem canonical2729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2729 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw2729 = injectiveMoment H raw2729step0 := by
      have heq : raw2729step0 = -raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2729).symm
    injectiveMoment H raw2729step0 = injectiveMoment H raw2729step1 := by
      have heq : raw2729step1 = (fun i j => raw2729step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2729step0 permutation8 permutation3
    _ = injectiveMoment H node27 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

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

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem sound153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node153 = Sparse.eval value153 (momentVector H) := by
  have heq : pivotMatrix153 = (fun u v => node153 (pivotPermutation153 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node153 = injectiveMoment H pivotMatrix153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix153 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix153 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (0 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node153 + (injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value153, value31, value35, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node162 = Sparse.eval value162 (momentVector H) := by
  have hc : momentVector H 124 = injectiveMoment H node162 := rfl
  simp [value162, Sparse.eval, hc]

theorem sound163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node163 = Sparse.eval value163 (momentVector H) := by
  have hc : momentVector H 125 = injectiveMoment H node163 := rfl
  simp [value163, Sparse.eval, hc]

theorem sound166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node166 = Sparse.eval value166 (momentVector H) := by
  have heq : pivotMatrix166 = (fun u v => node166 (pivotPermutation166 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node166 = injectiveMoment H pivotMatrix166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix166 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix166 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix166 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix166 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix166 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (2 : Fin 3) = raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2729 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node166 + (injectiveMoment H (mergeFirst pivotMatrix166 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix166 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix166 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value166, value27, value40, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node167 = Sparse.eval value167 (momentVector H) := by
  have hc : momentVector H 126 = injectiveMoment H node167 := rfl
  simp [value167, Sparse.eval, hc]

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

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
  linarith

theorem sound180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node180 = Sparse.eval value180 (momentVector H) := by
  have heq : pivotMatrix180 = (fun u v => node180 (pivotPermutation180 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node180 = injectiveMoment H pivotMatrix180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix180 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix180 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (2 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node180 + (injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value180, value36, value40, value63, Sparse.eval] at hc ⊢
  linarith

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

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

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

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node212 = Sparse.eval value212 (momentVector H) := by
  have hc : momentVector H 55 = injectiveMoment H node212 := rfl
  simp [value212, Sparse.eval, hc]

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

theorem sound280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node280 = Sparse.eval value280 (momentVector H) := by
  have heq : pivotMatrix280 = (fun u v => node280 (pivotPermutation280 u) v) := by apply Matrix.ext; unfold pivotMatrix280 node280 pivotPermutation280; decide +kernel
  have hmoment : injectiveMoment H node280 = injectiveMoment H pivotMatrix280 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix280 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix280 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix280 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (0 : Fin 3) = raw8560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw8560; decide +kernel
    rw [heq]
    exact (canonical8560 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix280 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (1 : Fin 3) = raw6880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw6880; decide +kernel
    rw [heq]
    exact (canonical6880 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix280 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (2 : Fin 3) = raw6789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw6789; decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node280 + (injectiveMoment H (mergeFirst pivotMatrix280 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix280 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix280 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value280, value10, value52, value63, Sparse.eval] at hc ⊢
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

theorem sound1056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1056 = Sparse.eval value1056 (momentVector H) := by
  have heq : pivotMatrix1056 = (fun u v => node1056.transpose (pivotPermutation1056 u) v) := by apply Matrix.ext; unfold pivotMatrix1056 node1056 pivotPermutation1056; decide +kernel
  have hmoment : injectiveMoment H node1056 = injectiveMoment H pivotMatrix1056 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1056 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1056 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1056 (0 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (0 : Fin 3) = raw4195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw4195; decide +kernel
    rw [heq]
    exact (canonical4195 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1056 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (1 : Fin 3) = raw7536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw7536; decide +kernel
    rw [heq]
    exact (canonical7536 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1056 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (2 : Fin 3) = raw7589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw7589; decide +kernel
    rw [heq]
    exact (canonical7589 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1056 + (injectiveMoment H (mergeFirst pivotMatrix1056 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1056 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1056 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1056, value177, value184, value185, Sparse.eval] at hc ⊢
  linarith

theorem sound1081 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1081 = Sparse.eval value1081 (momentVector H) := by
  have heq : pivotMatrix1081 = (fun u v => node1081 (pivotPermutation1081 u) v) := by apply Matrix.ext; unfold pivotMatrix1081 node1081 pivotPermutation1081; decide +kernel
  have hmoment : injectiveMoment H node1081 = injectiveMoment H pivotMatrix1081 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1081 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1081 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1081 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1081 (0 : Fin 3) = raw7245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1081 raw7245; decide +kernel
    rw [heq]
    exact (canonical7245 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1081 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1081 (1 : Fin 3) = raw6559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1081 raw6559; decide +kernel
    rw [heq]
    exact (canonical6559 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1081 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1081 (2 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1081 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1081 + (injectiveMoment H (mergeFirst pivotMatrix1081 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1081 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1081 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1081, value181, value185, Sparse.eval] at hc ⊢
  linarith

theorem sound1083 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1083 = Sparse.eval value1083 (momentVector H) := by
  have heq : pivotMatrix1083 = (fun u v => node1083 (pivotPermutation1083 u) v) := by apply Matrix.ext; unfold pivotMatrix1083 node1083 pivotPermutation1083; decide +kernel
  have hmoment : injectiveMoment H node1083 = injectiveMoment H pivotMatrix1083 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1083 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1083 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1083 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1083 (0 : Fin 3) = raw7356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1083 raw7356; decide +kernel
    rw [heq]
    exact (canonical7356 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1083 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1083 (1 : Fin 3) = raw6560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1083 raw6560; decide +kernel
    rw [heq]
    exact (canonical6560 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1083 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1083 (2 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1083 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1083 + (injectiveMoment H (mergeFirst pivotMatrix1083 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1083 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1083 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1083, value153, value185, value272, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound19
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1235 = Sparse.eval value1235 (momentVector H) := by
  have heq : pivotMatrix1235 = (fun u v => node1235.transpose (pivotPermutation1235 u) v) := by apply Matrix.ext; unfold pivotMatrix1235 node1235 pivotPermutation1235; decide +kernel
  have hmoment : injectiveMoment H node1235 = injectiveMoment H pivotMatrix1235 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1235 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1235 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1235 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1235 (0 : Fin 3) = raw5819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1235 raw5819; decide +kernel
    rw [heq]
    exact (canonical5819 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1235 (1 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1235 (1 : Fin 3) = raw8236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1235 raw8236; decide +kernel
    rw [heq]
    exact (canonical8236 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1235 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1235 (2 : Fin 3) = raw8246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1235 raw8246; decide +kernel
    rw [heq]
    exact (canonical8246 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1235 + (injectiveMoment H (mergeFirst pivotMatrix1235 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1235 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1235 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1235, value111, value177, Sparse.eval] at hc ⊢
  linarith

theorem sound1248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1248 = Sparse.eval value1248 (momentVector H) := by
  have heq : pivotMatrix1248 = (fun u v => node1248.transpose (pivotPermutation1248 u) v) := by apply Matrix.ext; unfold pivotMatrix1248 node1248 pivotPermutation1248; decide +kernel
  have hmoment : injectiveMoment H node1248 = injectiveMoment H pivotMatrix1248 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1248 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1248 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1248 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1248 (0 : Fin 3) = raw6908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1248 raw6908; decide +kernel
    rw [heq]
    exact (canonical6908 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1248 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1248 (1 : Fin 3) = raw8897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1248 raw8897; decide +kernel
    rw [heq]
    exact (canonical8897 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1248 (2 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1248 (2 : Fin 3) = raw8910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1248 raw8910; decide +kernel
    rw [heq]
    exact (canonical8910 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1248 + (injectiveMoment H (mergeFirst pivotMatrix1248 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1248 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1248 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1248, value180, value184, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1310 = Sparse.eval value1310 (momentVector H) := by
  have heq : pivotMatrix1310 = (fun u v => node1310.transpose (pivotPermutation1310 u) v) := by apply Matrix.ext; unfold pivotMatrix1310 node1310 pivotPermutation1310; decide +kernel
  have hmoment : injectiveMoment H node1310 = injectiveMoment H pivotMatrix1310 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1310 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1310 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1310 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (0 : Fin 3) = raw6950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw6950; decide +kernel
    rw [heq]
    exact (canonical6950 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1310 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (1 : Fin 3) = raw8928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw8928; decide +kernel
    rw [heq]
    exact (canonical8928 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1310 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (2 : Fin 3) = raw8934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw8934; decide +kernel
    rw [heq]
    exact (canonical8934 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1310 + (injectiveMoment H (mergeFirst pivotMatrix1310 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1310 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1310 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1310, value167, value175, value184, Sparse.eval] at hc ⊢
  linarith

theorem sound1315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1315 = Sparse.eval value1315 (momentVector H) := by
  have heq : pivotMatrix1315 = (fun u v => node1315.transpose (pivotPermutation1315 u) v) := by apply Matrix.ext; unfold pivotMatrix1315 node1315 pivotPermutation1315; decide +kernel
  have hmoment : injectiveMoment H node1315 = injectiveMoment H pivotMatrix1315 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1315 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1315 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (0 : Fin 3) = raw7606 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw7606; decide +kernel
    rw [heq]
    exact (canonical7606 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (1 : Fin 3) = raw9987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9987; decide +kernel
    rw [heq]
    exact (canonical9987 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (2 : Fin 3) = raw9991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9991; decide +kernel
    rw [heq]
    exact (canonical9991 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1315 + (injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1315, value162, value169, value184, Sparse.eval] at hc ⊢
  linarith

theorem sound1317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1317 = Sparse.eval value1317 (momentVector H) := by
  have heq : pivotMatrix1317 = (fun u v => node1317 (pivotPermutation1317 u) v) := by apply Matrix.ext; unfold pivotMatrix1317 node1317 pivotPermutation1317; decide +kernel
  have hmoment : injectiveMoment H node1317 = injectiveMoment H pivotMatrix1317 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1317 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1317 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1317 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (0 : Fin 3) = raw7512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7512; decide +kernel
    rw [heq]
    exact (canonical7512 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1317 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (1 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1317 (2 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (2 : Fin 3) = raw7592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7592; decide +kernel
    rw [heq]
    exact (canonical7592 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1317 + (injectiveMoment H (mergeFirst pivotMatrix1317 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1317 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1317 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1317, value166, value169, value280, Sparse.eval] at hc ⊢
  linarith

theorem sound1322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1322 = Sparse.eval value1322 (momentVector H) := by
  have heq : pivotMatrix1322 = (fun u v => node1322.transpose (pivotPermutation1322 u) v) := by apply Matrix.ext; unfold pivotMatrix1322 node1322 pivotPermutation1322; decide +kernel
  have hmoment : injectiveMoment H node1322 = injectiveMoment H pivotMatrix1322 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1322 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1322 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1322 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1322 (0 : Fin 3) = raw7608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1322 raw7608; decide +kernel
    rw [heq]
    exact (canonical7608 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1322 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1322 (1 : Fin 3) = raw9990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1322 raw9990; decide +kernel
    rw [heq]
    exact (canonical9990 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1322 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1322 (2 : Fin 3) = raw9993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1322 raw9993; decide +kernel
    rw [heq]
    exact (canonical9993 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1322 + (injectiveMoment H (mergeFirst pivotMatrix1322 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1322 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1322 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1322, value163, value197, value212, Sparse.eval] at hc ⊢
  linarith

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

theorem sound591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node591 = Sparse.eval value591 (momentVector H) := by
  have hc : momentVector H 140 = injectiveMoment H node591 := rfl
  simp [value591, Sparse.eval, hc]

theorem sound593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node593 = Sparse.eval value593 (momentVector H) := by
  have hc : momentVector H 538 = injectiveMoment H node593 := rfl
  simp [value593, Sparse.eval, hc]

theorem sound598 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node598 = Sparse.eval value598 (momentVector H) := by
  have hc : momentVector H 142 = injectiveMoment H node598 := rfl
  simp [value598, Sparse.eval, hc]

theorem sound602 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node602 = Sparse.eval value602 (momentVector H) := by
  have hc : momentVector H 145 = injectiveMoment H node602 := rfl
  simp [value602, Sparse.eval, hc]

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

theorem sound480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node480 = Sparse.eval value480 (momentVector H) := by
  have hc : momentVector H 383 = injectiveMoment H node480 := rfl
  simp [value480, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound30
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1982 = Sparse.eval value1982 (momentVector H) := by
  have heq : pivotMatrix1982 = (fun u v => node1982 (pivotPermutation1982 u) v) := by apply Matrix.ext; unfold pivotMatrix1982 node1982 pivotPermutation1982; decide +kernel
  have hmoment : injectiveMoment H node1982 = injectiveMoment H pivotMatrix1982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1982 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1982 (0 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (0 : Fin 4) = raw4427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw4427; decide +kernel
    rw [heq]
    exact (canonical4427 hH).trans (sound1248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1982 (1 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (1 : Fin 4) = raw3270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw3270; decide +kernel
    rw [heq]
    exact (canonical3270 hH).trans (sound1235 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1982 (2 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (2 : Fin 4) = raw3244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw3244; decide +kernel
    rw [heq]
    exact (canonical3244 hH).trans (sound1081 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1982 (3 : Fin 4)) =
      Sparse.eval value598 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (3 : Fin 4) = raw3242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw3242; decide +kernel
    rw [heq]
    exact (canonical3242 hH).trans (sound598 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1982 + (injectiveMoment H (mergeFirst pivotMatrix1982 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1982 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1982 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1982 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1982, value1081, value1235, value1248, value598, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound31
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2008 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2008 = Sparse.eval value2008 (momentVector H) := by
  have heq : pivotMatrix2008 = (fun u v => node2008 (pivotPermutation2008 u) v) := by apply Matrix.ext; unfold pivotMatrix2008 node2008 pivotPermutation2008; decide +kernel
  have hmoment : injectiveMoment H node2008 = injectiveMoment H pivotMatrix2008 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2008 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2008 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2008 (0 : Fin 4)) =
      Sparse.eval value480 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (0 : Fin 4) = raw1965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw1965; decide +kernel
    rw [heq]
    exact (canonical1965 hH).trans (sound480 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2008 (1 : Fin 4)) =
      Sparse.eval value602 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (1 : Fin 4) = raw3417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw3417; decide +kernel
    rw [heq]
    exact (canonical3417 hH).trans (sound602 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2008 (2 : Fin 4)) =
      Sparse.eval value1322 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (2 : Fin 4) = raw3496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw3496; decide +kernel
    rw [heq]
    exact (canonical3496 hH).trans (sound1322 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2008 (3 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (3 : Fin 4) = raw3504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw3504; decide +kernel
    rw [heq]
    exact (canonical3504 hH).trans (sound591 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2008 + (injectiveMoment H (mergeFirst pivotMatrix2008 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2008 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2008 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2008 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2008, value1322, value480, value591, value602, Sparse.eval] at hc ⊢
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

theorem sound2146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2146 = Sparse.eval value2146 (momentVector H) := by
  have heq : pivotMatrix2146 = (fun u v => node2146 (pivotPermutation2146 u) v) := by apply Matrix.ext; unfold pivotMatrix2146 node2146 pivotPermutation2146; decide +kernel
  have hmoment : injectiveMoment H node2146 = injectiveMoment H pivotMatrix2146 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2146 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2146 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2146 (0 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (0 : Fin 4) = raw5095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw5095; decide +kernel
    rw [heq]
    exact (canonical5095 hH).trans (sound593 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2146 (1 : Fin 4)) =
      Sparse.eval value598 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (1 : Fin 4) = raw4232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw4232; decide +kernel
    rw [heq]
    exact (canonical4232 hH).trans (sound598 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2146 (2 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (2 : Fin 4) = raw4230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw4230; decide +kernel
    rw [heq]
    exact (canonical4230 hH).trans (sound1056 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2146 (3 : Fin 4)) =
      Sparse.eval value480 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (3 : Fin 4) = raw4229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw4229; decide +kernel
    rw [heq]
    exact (canonical4229 hH).trans (sound480 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2146 + (injectiveMoment H (mergeFirst pivotMatrix2146 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2146 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2146 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2146 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2146, value1056, value480, value593, value598, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound34
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2216 = Sparse.eval value2216 (momentVector H) := by
  have heq : pivotMatrix2216 = (fun u v => node2216 (pivotPermutation2216 u) v) := by apply Matrix.ext; unfold pivotMatrix2216 node2216 pivotPermutation2216; decide +kernel
  have hmoment : injectiveMoment H node2216 = injectiveMoment H pivotMatrix2216 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2216 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2216 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2216 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (0 : Fin 4) = raw5329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw5329; decide +kernel
    rw [heq]
    exact (canonical5329 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2216 (1 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (1 : Fin 4) = raw4609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4609; decide +kernel
    rw [heq]
    exact (canonical4609 hH).trans (sound1310 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2216 (2 : Fin 4)) =
      Sparse.eval value1317 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (2 : Fin 4) = raw4504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4504; decide +kernel
    rw [heq]
    exact (canonical4504 hH).trans (sound1317 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2216 (3 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (3 : Fin 4) = raw4501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4501; decide +kernel
    rw [heq]
    exact (canonical4501 hH).trans (sound593 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2216 + (injectiveMoment H (mergeFirst pivotMatrix2216 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2216, value1310, value1315, value1317, value593, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound43
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2760 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2760 = Sparse.eval value2760 (momentVector H) := by
  have heq : pivotMatrix2760 = (fun u v => node2760 (pivotPermutation2760 u) v) := by apply Matrix.ext; unfold pivotMatrix2760 node2760 pivotPermutation2760; decide +kernel
  have hmoment : injectiveMoment H node2760 = injectiveMoment H pivotMatrix2760 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2760 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2760 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2760 (0 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2760 (0 : Fin 4) = raw6506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2760 raw6506; decide +kernel
    rw [heq]
    exact (canonical6506 hH).trans (sound1056 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2760 (1 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2760 (1 : Fin 4) = raw8366 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2760 raw8366; decide +kernel
    rw [heq]
    exact (canonical8366 hH).trans (sound1081 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2760 (2 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2760 (2 : Fin 4) = raw8487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2760 raw8487; decide +kernel
    rw [heq]
    exact (canonical8487 hH).trans (sound1083 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2760 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2760 (3 : Fin 4) = raw8496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2760 raw8496; decide +kernel
    rw [heq]
    exact (canonical8496 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2760 + (injectiveMoment H (mergeFirst pivotMatrix2760 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2760 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2760 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2760 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2760, value1056, value1081, value1083, value185, Sparse.eval] at hc ⊢
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

theorem sound3220_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3220 = Sparse.eval value3220 (momentVector H) := by
  have heq : pivotMatrix3220 = (fun u v => node3220 (pivotPermutation3220 u) v) := by apply Matrix.ext; unfold pivotMatrix3220 node3220 pivotPermutation3220; decide +kernel
  have hmoment : injectiveMoment H node3220 = injectiveMoment H pivotMatrix3220 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3220 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3220 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3220 (0 : Fin 5)) =
      Sparse.eval value2216 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3220 (0 : Fin 5) = raw5094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3220 raw5094; decide +kernel
    rw [heq]
    exact (canonical5094 hH).trans (sound2216 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3220 (1 : Fin 5)) =
      Sparse.eval value1982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3220 (1 : Fin 5) = raw4231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3220 raw4231; decide +kernel
    rw [heq]
    exact (canonical4231 hH).trans (sound1982 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3220 (2 : Fin 5)) =
      Sparse.eval value2008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3220 (2 : Fin 5) = raw4228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3220 raw4228; decide +kernel
    rw [heq]
    exact (canonical4228 hH).trans (sound2008 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3220 (3 : Fin 5)) =
      Sparse.eval value2760 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3220 (3 : Fin 5) = raw4227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3220 raw4227; decide +kernel
    rw [heq]
    exact (canonical4227 hH).trans (sound2760 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3220 (4 : Fin 5)) =
      Sparse.eval value2146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3220 (4 : Fin 5) = raw4226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3220 raw4226; decide +kernel
    rw [heq]
    exact (canonical4226 hH).trans (sound2146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3220 + (injectiveMoment H (mergeFirst pivotMatrix3220 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3220 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3220 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3220 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3220 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3220, value1982, value2008, value2146, value2216, value2760, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3220_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3220_e_oai
