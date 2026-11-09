-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3124_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T05:59:46.921027+00:00
-- url     : https://prove2.me/submissions/48a4253f-6766-4676-8801-0e85d6955e61

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2492_e

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

theorem canonical328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw328 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw328 = injectiveMoment H raw328step0 := by
      have heq : raw328step0 = raw328.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw328).symm
    injectiveMoment H raw328step0 = injectiveMoment H raw328step1 := by
      have heq : raw328step1 = -raw328step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw328step0).symm
    injectiveMoment H raw328step1 = injectiveMoment H raw328step2 := by
      have heq : raw328step2 = (fun i j => raw328step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw328step1 permutation4 permutation6
    _ = injectiveMoment H node59 := by rfl

theorem canonical336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw336 = injectiveMoment H node38 := by
  calc
    injectiveMoment H raw336 = injectiveMoment H raw336step0 := by
      have heq : raw336step0 = raw336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw336).symm
    injectiveMoment H raw336step0 = injectiveMoment H raw336step1 := by
      have heq : raw336step1 = (fun i j => raw336step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw336step0 permutation6 permutation5
    _ = injectiveMoment H node38 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3213 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw3213 = injectiveMoment H raw3213step0 := by
      have heq : raw3213step0 = raw3213.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3213).symm
    injectiveMoment H raw3213step0 = injectiveMoment H raw3213step1 := by
      have heq : raw3213step1 = (fun i j => raw3213step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3213step0 permutation22 permutation17
    _ = injectiveMoment H node1278 := by rfl

theorem canonical3217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3217 = injectiveMoment H node985 := by
  calc
    injectiveMoment H raw3217 = injectiveMoment H raw3217step0 := by
      have heq : raw3217step0 = raw3217.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3217).symm
    injectiveMoment H raw3217step0 = injectiveMoment H raw3217step1 := by
      have heq : raw3217step1 = (fun i j => raw3217step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3217step0 permutation22 permutation17
    _ = injectiveMoment H node985 := by rfl

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

theorem canonical3854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3854 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw3854 = injectiveMoment H raw3854step0 := by
      have heq : raw3854step0 = raw3854.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3854).symm
    _ = injectiveMoment H node218 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical4048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4048 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw4048 = injectiveMoment H raw4048step0 := by
      have heq : raw4048step0 = -raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4048).symm
    injectiveMoment H raw4048step0 = injectiveMoment H raw4048step1 := by
      have heq : raw4048step1 = (fun i j => raw4048step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4048step0 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4291 = injectiveMoment H node1251 := by
  calc
    injectiveMoment H raw4291 = injectiveMoment H raw4291step0 := by
      have heq : raw4291step0 = raw4291.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4291).symm
    injectiveMoment H raw4291step0 = injectiveMoment H raw4291step1 := by
      have heq : raw4291step1 = -raw4291step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4291step0).symm
    injectiveMoment H raw4291step1 = injectiveMoment H raw4291step2 := by
      have heq : raw4291step2 = (fun i j => raw4291step1 (permutation13 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4291step1 permutation13 permutation24
    _ = injectiveMoment H node1251 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4963 = injectiveMoment H node42 := by
  rfl

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

theorem canonical4982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4982 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw4982 = injectiveMoment H raw4982step0 := by
      have heq : raw4982step0 = raw4982.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4982).symm
    injectiveMoment H raw4982step0 = injectiveMoment H raw4982step1 := by
      have heq : raw4982step1 = (fun i j => raw4982step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4982step0 permutation13 permutation3
    _ = injectiveMoment H node206 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5501 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw5501 = injectiveMoment H raw5501step0 := by
      have heq : raw5501step0 = -raw5501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5501).symm
    injectiveMoment H raw5501step0 = injectiveMoment H raw5501step1 := by
      have heq : raw5501step1 = (fun i j => raw5501step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5501step0 permutation8 permutation3
    _ = injectiveMoment H node40 := by rfl

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

theorem canonical5986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5986 = injectiveMoment H node59 := by
  rfl

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

theorem canonical5994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5994 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw5994 = injectiveMoment H raw5994step0 := by
      have heq : raw5994step0 = raw5994.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5994).symm
    injectiveMoment H raw5994step0 = injectiveMoment H raw5994step1 := by
      have heq : raw5994step1 = (fun i j => raw5994step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5994step0 permutation32 permutation31
    _ = injectiveMoment H node1063 := by rfl

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

theorem canonical6298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6298 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6298 = injectiveMoment H raw6298step0 := by
      have heq : raw6298step0 = raw6298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6298).symm
    injectiveMoment H raw6298step0 = injectiveMoment H raw6298step1 := by
      have heq : raw6298step1 = (fun i j => raw6298step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6298step0 permutation25 permutation7
    _ = injectiveMoment H node188 := by rfl

theorem canonical6299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6299 = injectiveMoment H node90 := by
  calc
    injectiveMoment H raw6299 = injectiveMoment H raw6299step0 := by
      have heq : raw6299step0 = raw6299.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6299).symm
    injectiveMoment H raw6299step0 = injectiveMoment H raw6299step1 := by
      have heq : raw6299step1 = (fun i j => raw6299step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6299step0 permutation21 permutation7
    _ = injectiveMoment H node90 := by rfl

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

theorem canonical6304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6304 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6304 = injectiveMoment H raw6304step0 := by
      have heq : raw6304step0 = raw6304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6304).symm
    injectiveMoment H raw6304step0 = injectiveMoment H raw6304step1 := by
      have heq : raw6304step1 = (fun i j => raw6304step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6304step0 permutation21 permutation5
    _ = injectiveMoment H node173 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6337 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6337 = injectiveMoment H raw6337step0 := by
      have heq : raw6337step0 = raw6337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6337).symm
    injectiveMoment H raw6337step0 = injectiveMoment H raw6337step1 := by
      have heq : raw6337step1 = (fun i j => raw6337step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6337step0 permutation23 permutation5
    _ = injectiveMoment H node173 := by rfl

theorem canonical6338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6338 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6338 = injectiveMoment H raw6338step0 := by
      have heq : raw6338step0 = raw6338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6338).symm
    injectiveMoment H raw6338step0 = injectiveMoment H raw6338step1 := by
      have heq : raw6338step1 = (fun i j => raw6338step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6338step0 permutation21 permutation7
    _ = injectiveMoment H node173 := by rfl

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

theorem canonical6519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6519 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6519 = injectiveMoment H raw6519step0 := by
      have heq : raw6519step0 = raw6519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6519).symm
    injectiveMoment H raw6519step0 = injectiveMoment H raw6519step1 := by
      have heq : raw6519step1 = -raw6519step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6519step0).symm
    injectiveMoment H raw6519step1 = injectiveMoment H raw6519step2 := by
      have heq : raw6519step2 = (fun i j => raw6519step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6519step1 permutation31 permutation4
    _ = injectiveMoment H node188 := by rfl

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

theorem canonical6567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6567 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6567 = injectiveMoment H raw6567step0 := by
      have heq : raw6567step0 = raw6567.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6567).symm
    injectiveMoment H raw6567step0 = injectiveMoment H raw6567step1 := by
      have heq : raw6567step1 = -raw6567step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6567step0).symm
    injectiveMoment H raw6567step1 = injectiveMoment H raw6567step2 := by
      have heq : raw6567step2 = (fun i j => raw6567step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6567step1 permutation32 permutation4
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
  rfl

theorem canonical6875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6875 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6875 = injectiveMoment H raw6875step0 := by
      have heq : raw6875step0 = -raw6875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6875).symm
    injectiveMoment H raw6875step0 = injectiveMoment H raw6875step1 := by
      have heq : raw6875step1 = (fun i j => raw6875step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6875step0 permutation8 permutation4
    _ = injectiveMoment H node59 := by rfl

theorem canonical6877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6877 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6877 = injectiveMoment H raw6877step0 := by
      have heq : raw6877step0 = -raw6877 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6877).symm
    injectiveMoment H raw6877step0 = injectiveMoment H raw6877step1 := by
      have heq : raw6877step1 = (fun i j => raw6877step0 (permutation6 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6877step0 permutation6 permutation4
    _ = injectiveMoment H node59 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6912 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw6912 = injectiveMoment H raw6912step0 := by
      have heq : raw6912step0 = raw6912.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6912).symm
    injectiveMoment H raw6912step0 = injectiveMoment H raw6912step1 := by
      have heq : raw6912step1 = -raw6912step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6912step0).symm
    injectiveMoment H raw6912step1 = injectiveMoment H raw6912step2 := by
      have heq : raw6912step2 = (fun i j => raw6912step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6912step1 permutation25 permutation4
    _ = injectiveMoment H node225 := by rfl

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

theorem canonical6947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6947 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw6947 = injectiveMoment H raw6947step0 := by
      have heq : raw6947step0 = raw6947.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6947).symm
    injectiveMoment H raw6947step0 = injectiveMoment H raw6947step1 := by
      have heq : raw6947step1 = -raw6947step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6947step0).symm
    injectiveMoment H raw6947step1 = injectiveMoment H raw6947step2 := by
      have heq : raw6947step2 = (fun i j => raw6947step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6947step1 permutation25 permutation3
    _ = injectiveMoment H node206 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7001 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw7001 = injectiveMoment H raw7001step0 := by
      have heq : raw7001step0 = raw7001.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7001).symm
    injectiveMoment H raw7001step0 = injectiveMoment H raw7001step1 := by
      have heq : raw7001step1 = -raw7001step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7001step0).symm
    injectiveMoment H raw7001step1 = injectiveMoment H raw7001step2 := by
      have heq : raw7001step2 = (fun i j => raw7001step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7001step1 permutation21 permutation6
    _ = injectiveMoment H node173 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7223 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7223 = injectiveMoment H raw7223step0 := by
      have hz : ∀ i, raw7223 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7223step0 = (fun i j => raw7223 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7223 permutation15 hz
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical7249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7249 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7249 = injectiveMoment H raw7249step0 := by
      have heq : raw7249step0 = raw7249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7249).symm
    injectiveMoment H raw7249step0 = injectiveMoment H raw7249step1 := by
      have heq : raw7249step1 = (fun i j => raw7249step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7249step0 permutation21 permutation7
    _ = injectiveMoment H node174 := by rfl

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

theorem canonical7480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7480 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw7480 = injectiveMoment H raw7480step0 := by
      have heq : raw7480step0 = raw7480.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7480).symm
    injectiveMoment H raw7480step0 = injectiveMoment H raw7480step1 := by
      have heq : raw7480step1 = (fun i j => raw7480step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7480step0 permutation13 permutation3
    _ = injectiveMoment H node286 := by rfl

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

theorem canonical7514 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7514 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7514 = injectiveMoment H raw7514step0 := by
      have heq : raw7514step0 = raw7514.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7514).symm
    injectiveMoment H raw7514step0 = injectiveMoment H raw7514step1 := by
      have heq : raw7514step1 = -raw7514step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7514step0).symm
    injectiveMoment H raw7514step1 = injectiveMoment H raw7514step2 := by
      have heq : raw7514step2 = (fun i j => raw7514step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7514step1 permutation26 permutation4
    _ = injectiveMoment H node281 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7915 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw7915 = injectiveMoment H raw7915step0 := by
      have heq : raw7915step0 = raw7915.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7915).symm
    injectiveMoment H raw7915step0 = injectiveMoment H raw7915step1 := by
      have heq : raw7915step1 = -raw7915step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7915step0).symm
    injectiveMoment H raw7915step1 = injectiveMoment H raw7915step2 := by
      have heq : raw7915step2 = (fun i j => raw7915step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7915step1 permutation24 permutation3
    _ = injectiveMoment H node246 := by rfl

theorem canonical7923 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7923 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw7923 = injectiveMoment H raw7923step0 := by
      have heq : raw7923step0 = raw7923.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7923).symm
    injectiveMoment H raw7923step0 = injectiveMoment H raw7923step1 := by
      have heq : raw7923step1 = -raw7923step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7923step0).symm
    injectiveMoment H raw7923step1 = injectiveMoment H raw7923step2 := by
      have heq : raw7923step2 = (fun i j => raw7923step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7923step1 permutation23 permutation3
    _ = injectiveMoment H node246 := by rfl

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

theorem canonical7995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7995 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7995 = injectiveMoment H raw7995step0 := by
      have heq : raw7995step0 = (fun i j => raw7995 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7995 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8048 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw8048 = injectiveMoment H raw8048step0 := by
      have hz : ∀ i, raw8048 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8048step0 = (fun i j => raw8048 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8048 permutation9 hz
    _ = injectiveMoment H node40 := by rfl

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

theorem canonical8171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8171 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw8171 = injectiveMoment H raw8171step0 := by
      have hz : ∀ i, raw8171 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8171step0 = (fun i j => raw8171 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8171 permutation3 hz
    injectiveMoment H raw8171step0 = injectiveMoment H raw8171step1 := by
      have heq : raw8171step1 = (fun i j => raw8171step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8171step0 permutation7 permutation2
    _ = injectiveMoment H node9 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8269 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw8269 = injectiveMoment H raw8269step0 := by
      have heq : raw8269step0 = raw8269.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8269).symm
    injectiveMoment H raw8269step0 = injectiveMoment H raw8269step1 := by
      have heq : raw8269step1 = (fun i j => raw8269step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8269step0 permutation32 permutation31
    _ = injectiveMoment H node977 := by rfl

theorem canonical8270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8270 = injectiveMoment H node1267 := by
  calc
    injectiveMoment H raw8270 = injectiveMoment H raw8270step0 := by
      have heq : raw8270step0 = raw8270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8270).symm
    injectiveMoment H raw8270step0 = injectiveMoment H raw8270step1 := by
      have heq : raw8270step1 = (fun i j => raw8270step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8270step0 permutation32 permutation31
    _ = injectiveMoment H node1267 := by rfl

theorem canonical8271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8271 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8271 = injectiveMoment H raw8271step0 := by
      have heq : raw8271step0 = raw8271.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8271).symm
    injectiveMoment H raw8271step0 = injectiveMoment H raw8271step1 := by
      have hz : ∀ j, raw8271step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8271step1 = (fun i j => raw8271step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8271step0 permutation9 hz
    injectiveMoment H raw8271step1 = injectiveMoment H raw8271step2 := by
      have hz : ∀ i, raw8271step1 i (permutation27 0) = 0 := by decide +kernel
      have heq : raw8271step2 = (fun i j => raw8271step1 i (permutation27 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8271step1 permutation27 hz
    injectiveMoment H raw8271step2 = injectiveMoment H raw8271step3 := by
      have heq : raw8271step3 = (fun i j => raw8271step2 (permutation8 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8271step2 permutation8 permutation7
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8302 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw8302 = injectiveMoment H raw8302step0 := by
      have hz : ∀ i, raw8302 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8302step0 = (fun i j => raw8302 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8302 permutation9 hz
    _ = injectiveMoment H node59 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8337 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8337 = injectiveMoment H raw8337step0 := by
      have hz : ∀ i, raw8337 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8337step0 = (fun i j => raw8337 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8337 permutation9 hz
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical8900 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8900 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw8900 = injectiveMoment H raw8900step0 := by
      have heq : raw8900step0 = raw8900.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8900).symm
    injectiveMoment H raw8900step0 = injectiveMoment H raw8900step1 := by
      have heq : raw8900step1 = -raw8900step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8900step0).symm
    injectiveMoment H raw8900step1 = injectiveMoment H raw8900step2 := by
      have heq : raw8900step2 = (fun i j => raw8900step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8900step1 permutation22 permutation4
    _ = injectiveMoment H node225 := by rfl

theorem canonical8913 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8913 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw8913 = injectiveMoment H raw8913step0 := by
      have heq : raw8913step0 = raw8913.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8913).symm
    injectiveMoment H raw8913step0 = injectiveMoment H raw8913step1 := by
      have heq : raw8913step1 = -raw8913step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8913step0).symm
    injectiveMoment H raw8913step1 = injectiveMoment H raw8913step2 := by
      have heq : raw8913step2 = (fun i j => raw8913step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8913step1 permutation22 permutation4
    _ = injectiveMoment H node228 := by rfl

theorem canonical8925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8925 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw8925 = injectiveMoment H raw8925step0 := by
      have heq : raw8925step0 = raw8925.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8925).symm
    injectiveMoment H raw8925step0 = injectiveMoment H raw8925step1 := by
      have heq : raw8925step1 = -raw8925step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8925step0).symm
    injectiveMoment H raw8925step1 = injectiveMoment H raw8925step2 := by
      have heq : raw8925step2 = (fun i j => raw8925step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8925step1 permutation22 permutation3
    _ = injectiveMoment H node206 := by rfl

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

theorem canonical8930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8930 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw8930 = injectiveMoment H raw8930step0 := by
      have heq : raw8930step0 = raw8930.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8930).symm
    injectiveMoment H raw8930step0 = injectiveMoment H raw8930step1 := by
      have heq : raw8930step1 = -raw8930step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8930step0).symm
    injectiveMoment H raw8930step1 = injectiveMoment H raw8930step2 := by
      have heq : raw8930step2 = (fun i j => raw8930step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8930step1 permutation22 permutation3
    _ = injectiveMoment H node201 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9070 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw9070 = injectiveMoment H raw9070step0 := by
      have hz : ∀ i, raw9070 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9070step0 = (fun i j => raw9070 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9070 permutation9 hz
    injectiveMoment H raw9070step0 = injectiveMoment H raw9070step1 := by
      have heq : raw9070step1 = (fun i j => raw9070step0 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9070step0 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical304
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9746 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw9746 = injectiveMoment H raw9746step0 := by
      have heq : raw9746step0 = raw9746.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9746).symm
    injectiveMoment H raw9746step0 = injectiveMoment H raw9746step1 := by
      have heq : raw9746step1 = -raw9746step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9746step0).symm
    injectiveMoment H raw9746step1 = injectiveMoment H raw9746step2 := by
      have heq : raw9746step2 = (fun i j => raw9746step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9746step1 permutation21 permutation4
    _ = injectiveMoment H node281 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical305
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9761 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw9761 = injectiveMoment H raw9761step0 := by
      have heq : raw9761step0 = raw9761.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9761).symm
    injectiveMoment H raw9761step0 = injectiveMoment H raw9761step1 := by
      have heq : raw9761step1 = (fun i j => raw9761step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9761step0 permutation27 permutation3
    _ = injectiveMoment H node286 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10099 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw10099 = injectiveMoment H raw10099step0 := by
      have heq : raw10099step0 = raw10099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10099).symm
    injectiveMoment H raw10099step0 = injectiveMoment H raw10099step1 := by
      have heq : raw10099step1 = (fun i j => raw10099step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10099step0 permutation27 permutation3
    _ = injectiveMoment H node225 := by rfl

theorem canonical10105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10105 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw10105 = injectiveMoment H raw10105step0 := by
      have heq : raw10105step0 = raw10105.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10105).symm
    injectiveMoment H raw10105step0 = injectiveMoment H raw10105step1 := by
      have heq : raw10105step1 = (fun i j => raw10105step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10105step0 permutation27 permutation3
    _ = injectiveMoment H node206 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1128 = injectiveMoment H node1070 := by
  calc
    injectiveMoment H raw1128 = injectiveMoment H raw1128step0 := by
      have heq : raw1128step0 = raw1128.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1128).symm
    injectiveMoment H raw1128step0 = injectiveMoment H raw1128step1 := by
      have heq : raw1128step1 = (fun i j => raw1128step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1128step0 permutation25 permutation17
    _ = injectiveMoment H node1070 := by rfl

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

theorem canonical1468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1468 = injectiveMoment H node1555 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1526 = injectiveMoment H node286 := by
  calc
    injectiveMoment H raw1526 = injectiveMoment H raw1526step0 := by
      have heq : raw1526step0 = raw1526.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1526).symm
    injectiveMoment H raw1526step0 = injectiveMoment H raw1526step1 := by
      have hz : ∀ i, raw1526step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw1526step1 = (fun i j => raw1526step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1526step0 permutation15 hz
    injectiveMoment H raw1526step1 = injectiveMoment H raw1526step2 := by
      have heq : raw1526step2 = (fun i j => raw1526step1 (permutation24 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1526step1 permutation24 permutation5
    _ = injectiveMoment H node286 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1664 = injectiveMoment H node1272 := by
  calc
    injectiveMoment H raw1664 = injectiveMoment H raw1664step0 := by
      have heq : raw1664step0 = raw1664.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1664).symm
    injectiveMoment H raw1664step0 = injectiveMoment H raw1664step1 := by
      have heq : raw1664step1 = (fun i j => raw1664step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1664step0 permutation25 permutation17
    _ = injectiveMoment H node1272 := by rfl

theorem canonical1667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1667 = injectiveMoment H node981 := by
  calc
    injectiveMoment H raw1667 = injectiveMoment H raw1667step0 := by
      have heq : raw1667step0 = raw1667.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1667).symm
    injectiveMoment H raw1667step0 = injectiveMoment H raw1667step1 := by
      have heq : raw1667step1 = (fun i j => raw1667step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1667step0 permutation25 permutation17
    _ = injectiveMoment H node981 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2042 = injectiveMoment H node1080 := by
  calc
    injectiveMoment H raw2042 = injectiveMoment H raw2042step0 := by
      have heq : raw2042step0 = raw2042.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2042).symm
    injectiveMoment H raw2042step0 = injectiveMoment H raw2042step1 := by
      have heq : raw2042step1 = (fun i j => raw2042step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2042step0 permutation22 permutation17
    _ = injectiveMoment H node1080 := by rfl

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

theorem canonical2864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2864 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2864 = injectiveMoment H raw2864step0 := by
      have heq : raw2864step0 = raw2864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2864).symm
    injectiveMoment H raw2864step0 = injectiveMoment H raw2864step1 := by
      have heq : raw2864step1 = (fun i j => raw2864step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2864step0 permutation6 permutation7
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3055 = injectiveMoment H node1940 := by
  rfl

theorem canonical3056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3056 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw3056 = injectiveMoment H raw3056step0 := by
      have heq : raw3056step0 = raw3056.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3056).symm
    injectiveMoment H raw3056step0 = injectiveMoment H raw3056step1 := by
      have heq : raw3056step1 = -raw3056step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3056step0).symm
    injectiveMoment H raw3056step1 = injectiveMoment H raw3056step2 := by
      have heq : raw3056step2 = (fun i j => raw3056step1 (permutation13 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3056step1 permutation13 permutation23
    _ = injectiveMoment H node1306 := by rfl

theorem canonical3057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3057 = injectiveMoment H node586 := by
  rfl

theorem canonical3064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3064 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw3064 = injectiveMoment H raw3064step0 := by
      have heq : raw3064step0 = raw3064.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3064).symm
    injectiveMoment H raw3064step0 = injectiveMoment H raw3064step1 := by
      have heq : raw3064step1 = -raw3064step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3064step0).symm
    injectiveMoment H raw3064step1 = injectiveMoment H raw3064step2 := by
      have heq : raw3064step2 = (fun i j => raw3064step1 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3064step1 permutation28 permutation17
    _ = injectiveMoment H node1171 := by rfl

theorem canonical3065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3065 = injectiveMoment H node2492 := by
  calc
    injectiveMoment H raw3065 = injectiveMoment H raw3065step0 := by
      have heq : raw3065step0 = -raw3065 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3065).symm
    injectiveMoment H raw3065step0 = injectiveMoment H raw3065step1 := by
      have heq : raw3065step1 = (fun i j => raw3065step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3065step0 permutation149 permutation15
    _ = injectiveMoment H node2492 := by rfl

theorem canonical3066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3066 = injectiveMoment H node1941 := by
  rfl

theorem canonical3067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3067 = injectiveMoment H node2746 := by
  calc
    injectiveMoment H raw3067 = injectiveMoment H raw3067step0 := by
      have heq : raw3067step0 = (fun i j => raw3067 (permutation62 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3067 permutation62 permutation16
    _ = injectiveMoment H node2746 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3116 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw3116 = injectiveMoment H raw3116step0 := by
      have heq : raw3116step0 = raw3116.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3116).symm
    injectiveMoment H raw3116step0 = injectiveMoment H raw3116step1 := by
      have heq : raw3116step1 = -raw3116step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3116step0).symm
    injectiveMoment H raw3116step1 = injectiveMoment H raw3116step2 := by
      have hz : ∀ i, raw3116step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw3116step2 = (fun i j => raw3116step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3116step1 permutation15 hz
    injectiveMoment H raw3116step2 = injectiveMoment H raw3116step3 := by
      have heq : raw3116step3 = (fun i j => raw3116step2 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3116step2 permutation27 permutation5
    _ = injectiveMoment H node246 := by rfl

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

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound38 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node38 = Sparse.eval value38 (momentVector H) := by
  have hc : momentVector H 128 = injectiveMoment H node38 := rfl
  simp [value38, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node42 = Sparse.eval value42 (momentVector H) := by
  have hc : momentVector H 11 = injectiveMoment H node42 := rfl
  simp [value42, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

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

theorem sound90 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node90 = Sparse.eval value90 (momentVector H) := by
  have heq : pivotMatrix90 = (fun u v => node90 (pivotPermutation90 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node90 = injectiveMoment H pivotMatrix90 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix90 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix90 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix90 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix90 (1 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (1 : Fin 3) = raw336 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical336 hH).trans (sound38 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix90 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (2 : Fin 3) = raw328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical328 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node90 + (injectiveMoment H (mergeFirst pivotMatrix90 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix90 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix90 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value90, value38, value59, Sparse.eval] at hc ⊢
  linarith

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

theorem sound173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node173 = Sparse.eval value173 (momentVector H) := by
  have heq : pivotMatrix173 = (fun u v => node173 (pivotPermutation173 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node173 = injectiveMoment H pivotMatrix173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix173 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix173 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node173 + (injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value173, value40, value59, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node174 = Sparse.eval value174 (momentVector H) := by
  have heq : pivotMatrix174 = (fun u v => node174 (pivotPermutation174 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node174 = injectiveMoment H pivotMatrix174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix174 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix174 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (2 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node174 + (injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value174, value52, value56, value63, Sparse.eval] at hc ⊢
  linarith

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

theorem sound188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node188 = Sparse.eval value188 (momentVector H) := by
  have heq : pivotMatrix188 = (fun u v => node188 (pivotPermutation188 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node188 = injectiveMoment H pivotMatrix188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix188 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix188 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (0 : Fin 3) = raw5982 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (1 : Fin 3) = raw2864 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2864 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node188 + (injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value188, value37, value58, value63, Sparse.eval] at hc ⊢
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

theorem sound201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node201 = Sparse.eval value201 (momentVector H) := by
  have heq : pivotMatrix201 = (fun u v => node201 (pivotPermutation201 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node201 = injectiveMoment H pivotMatrix201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix201 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix201 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (2 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node201 + (injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value201, value31, value32, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node206 = Sparse.eval value206 (momentVector H) := by
  have heq : pivotMatrix206 = (fun u v => node206 (pivotPermutation206 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node206 = injectiveMoment H pivotMatrix206 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix206 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix206 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (0 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node206 + (injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value206, value32, value36, value40, Sparse.eval] at hc ⊢
  linarith

theorem sound218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node218 = Sparse.eval value218 (momentVector H) := by
  have hc : momentVector H 201 = injectiveMoment H node218 := rfl
  simp [value218, Sparse.eval, hc]

theorem sound225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node225 = Sparse.eval value225 (momentVector H) := by
  have hc : momentVector H 228 = injectiveMoment H node225 := rfl
  simp [value225, Sparse.eval, hc]

theorem sound228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node228 = Sparse.eval value228 (momentVector H) := by
  have heq : pivotMatrix228 = (fun u v => node228 (pivotPermutation228 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node228 = injectiveMoment H pivotMatrix228 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix228 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix228 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix228 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (0 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix228 (1 : Fin 3)) =
      Sparse.eval value42 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (1 : Fin 3) = raw4963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4963 hH).trans (sound42 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix228 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (2 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node228 + (injectiveMoment H (mergeFirst pivotMatrix228 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix228 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix228 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value228, value32, value42, value43, Sparse.eval] at hc ⊢
  linarith

theorem sound246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node246 = Sparse.eval value246 (momentVector H) := by
  have heq : pivotMatrix246 = (fun u v => node246 (pivotPermutation246 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node246 = injectiveMoment H pivotMatrix246 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix246 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix246 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix246 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix246 (0 : Fin 3) = raw7995 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix246 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix246 (1 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix246 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix246 (2 : Fin 3) = raw5501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5501 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node246 + (injectiveMoment H (mergeFirst pivotMatrix246 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix246 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix246 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value246, value40, value52, value63, Sparse.eval] at hc ⊢
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

theorem sound281 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node281 = Sparse.eval value281 (momentVector H) := by
  have heq : pivotMatrix281 = (fun u v => node281 (pivotPermutation281 u) v) := by apply Matrix.ext; unfold pivotMatrix281 node281 pivotPermutation281; decide +kernel
  have hmoment : injectiveMoment H node281 = injectiveMoment H pivotMatrix281 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix281 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix281 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix281 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (0 : Fin 3) = raw8171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw8171; decide +kernel
    rw [heq]
    exact (canonical8171 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix281 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (1 : Fin 3) = raw6877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw6877; decide +kernel
    rw [heq]
    exact (canonical6877 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix281 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (2 : Fin 3) = raw6789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw6789; decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node281 + (injectiveMoment H (mergeFirst pivotMatrix281 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix281 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix281 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value281, value52, value59, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node286 = Sparse.eval value286 (momentVector H) := by
  have heq : pivotMatrix286 = (fun u v => node286 (pivotPermutation286 u) v) := by apply Matrix.ext; unfold pivotMatrix286 node286 pivotPermutation286; decide +kernel
  have hmoment : injectiveMoment H node286 = injectiveMoment H pivotMatrix286 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix286 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix286 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix286 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix286 (0 : Fin 3) = raw5986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix286 raw5986; decide +kernel
    rw [heq]
    exact (canonical5986 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix286 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix286 (1 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix286 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix286 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix286 (2 : Fin 3) = raw6875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix286 raw6875; decide +kernel
    rw [heq]
    exact (canonical6875 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node286 + (injectiveMoment H (mergeFirst pivotMatrix286 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix286 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix286 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value286, value59, value63, Sparse.eval] at hc ⊢
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

theorem sound977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node977 = Sparse.eval value977 (momentVector H) := by
  have heq : pivotMatrix977 = (fun u v => node977 (pivotPermutation977 u) v) := by apply Matrix.ext; unfold pivotMatrix977 node977 pivotPermutation977; decide +kernel
  have hmoment : injectiveMoment H node977 = injectiveMoment H pivotMatrix977 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix977 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix977 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (1 : Fin 3) = raw6338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6338; decide +kernel
    rw [heq]
    exact (canonical6338 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node977 + (injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value977, value173, value188, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound981 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node981 = Sparse.eval value981 (momentVector H) := by
  have heq : pivotMatrix981 = (fun u v => node981 (pivotPermutation981 u) v) := by apply Matrix.ext; unfold pivotMatrix981 node981 pivotPermutation981; decide +kernel
  have hmoment : injectiveMoment H node981 = injectiveMoment H pivotMatrix981 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix981 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix981 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix981 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix981 (0 : Fin 3) = raw8302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix981 raw8302; decide +kernel
    rw [heq]
    exact (canonical8302 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix981 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix981 (1 : Fin 3) = raw6338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix981 raw6338; decide +kernel
    rw [heq]
    exact (canonical6338 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix981 (2 : Fin 3)) =
      Sparse.eval value90 (momentVector H) := by
    have heq : mergeFirst pivotMatrix981 (2 : Fin 3) = raw6299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix981 raw6299; decide +kernel
    rw [heq]
    exact (canonical6299 hH).trans (sound90 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node981 + (injectiveMoment H (mergeFirst pivotMatrix981 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix981 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix981 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value981, value173, value59, value90, Sparse.eval] at hc ⊢
  linarith

theorem sound985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node985 = Sparse.eval value985 (momentVector H) := by
  have heq : pivotMatrix985 = (fun u v => node985 (pivotPermutation985 u) v) := by apply Matrix.ext; unfold pivotMatrix985 node985 pivotPermutation985; decide +kernel
  have hmoment : injectiveMoment H node985 = injectiveMoment H pivotMatrix985 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix985 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix985 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix985 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix985 (0 : Fin 3) = raw8048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix985 raw8048; decide +kernel
    rw [heq]
    exact (canonical8048 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix985 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix985 (1 : Fin 3) = raw6337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix985 raw6337; decide +kernel
    rw [heq]
    exact (canonical6337 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix985 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix985 (2 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix985 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node985 + (injectiveMoment H (mergeFirst pivotMatrix985 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix985 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix985 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value985, value173, value40, Sparse.eval] at hc ⊢
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

theorem sound1063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1063 = Sparse.eval value1063 (momentVector H) := by
  have heq : pivotMatrix1063 = (fun u v => node1063 (pivotPermutation1063 u) v) := by apply Matrix.ext; unfold pivotMatrix1063 node1063 pivotPermutation1063; decide +kernel
  have hmoment : injectiveMoment H node1063 = injectiveMoment H pivotMatrix1063 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1063 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1063 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1063 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1063 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (1 : Fin 3) = raw6567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw6567; decide +kernel
    rw [heq]
    exact (canonical6567 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1063 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1063 + (injectiveMoment H (mergeFirst pivotMatrix1063 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1063 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1063 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1063, value185, value188, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound1070 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1070 = Sparse.eval value1070 (momentVector H) := by
  have heq : pivotMatrix1070 = (fun u v => node1070.transpose (pivotPermutation1070 u) v) := by apply Matrix.ext; unfold pivotMatrix1070 node1070 pivotPermutation1070; decide +kernel
  have hmoment : injectiveMoment H node1070 = injectiveMoment H pivotMatrix1070 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1070 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1070 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1070 (0 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1070 (0 : Fin 3) = raw3854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1070 raw3854; decide +kernel
    rw [heq]
    exact (canonical3854 hH).trans (sound218 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1070 (1 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1070 (1 : Fin 3) = raw7480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1070 raw7480; decide +kernel
    rw [heq]
    exact (canonical7480 hH).trans (sound286 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1070 (2 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1070 (2 : Fin 3) = raw7514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1070 raw7514; decide +kernel
    rw [heq]
    exact (canonical7514 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1070 + (injectiveMoment H (mergeFirst pivotMatrix1070 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1070 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1070 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1070, value218, value281, value286, Sparse.eval] at hc ⊢
  linarith

theorem sound1080 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1080 = Sparse.eval value1080 (momentVector H) := by
  have heq : pivotMatrix1080 = (fun u v => node1080.transpose (pivotPermutation1080 u) v) := by apply Matrix.ext; unfold pivotMatrix1080 node1080 pivotPermutation1080; decide +kernel
  have hmoment : injectiveMoment H node1080 = injectiveMoment H pivotMatrix1080 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1080 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1080 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1080 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1080 (0 : Fin 3) = raw4982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1080 raw4982; decide +kernel
    rw [heq]
    exact (canonical4982 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1080 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1080 (1 : Fin 3) = raw7915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1080 raw7915; decide +kernel
    rw [heq]
    exact (canonical7915 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1080 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1080 (2 : Fin 3) = raw7923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1080 raw7923; decide +kernel
    rw [heq]
    exact (canonical7923 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1080 + (injectiveMoment H (mergeFirst pivotMatrix1080 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1080 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1080 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1080, value206, value246, Sparse.eval] at hc ⊢
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

theorem sound1171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1171 = Sparse.eval value1171 (momentVector H) := by
  have heq : pivotMatrix1171 = (fun u v => node1171 (pivotPermutation1171 u) v) := by apply Matrix.ext; unfold pivotMatrix1171 node1171 pivotPermutation1171; decide +kernel
  have hmoment : injectiveMoment H node1171 = injectiveMoment H pivotMatrix1171 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1171 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1171 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1171 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1171 (0 : Fin 3) = raw9070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1171 raw9070; decide +kernel
    rw [heq]
    exact (canonical9070 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1171 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1171 (1 : Fin 3) = raw7041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1171 raw7041; decide +kernel
    rw [heq]
    exact (canonical7041 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1171 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1171 (2 : Fin 3) = raw7001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1171 raw7001; decide +kernel
    rw [heq]
    exact (canonical7001 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1171 + (injectiveMoment H (mergeFirst pivotMatrix1171 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1171 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1171 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1171, value149, value173, value63, Sparse.eval] at hc ⊢
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

theorem sound1251 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1251 = Sparse.eval value1251 (momentVector H) := by
  have heq : pivotMatrix1251 = (fun u v => node1251.transpose (pivotPermutation1251 u) v) := by apply Matrix.ext; unfold pivotMatrix1251 node1251 pivotPermutation1251; decide +kernel
  have hmoment : injectiveMoment H node1251 = injectiveMoment H pivotMatrix1251 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1251 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1251 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1251 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1251 (0 : Fin 3) = raw6912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1251 raw6912; decide +kernel
    rw [heq]
    exact (canonical6912 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1251 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1251 (1 : Fin 3) = raw8900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1251 raw8900; decide +kernel
    rw [heq]
    exact (canonical8900 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1251 (2 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1251 (2 : Fin 3) = raw8913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1251 raw8913; decide +kernel
    rw [heq]
    exact (canonical8913 hH).trans (sound228 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1251 + (injectiveMoment H (mergeFirst pivotMatrix1251 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1251 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1251 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1251, value225, value228, Sparse.eval] at hc ⊢
  linarith

theorem sound1267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1267 = Sparse.eval value1267 (momentVector H) := by
  have heq : pivotMatrix1267 = (fun u v => node1267 (pivotPermutation1267 u) v) := by apply Matrix.ext; unfold pivotMatrix1267 node1267 pivotPermutation1267; decide +kernel
  have hmoment : injectiveMoment H node1267 = injectiveMoment H pivotMatrix1267 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1267 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1267 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1267 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1267 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (1 : Fin 3) = raw7249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw7249; decide +kernel
    rw [heq]
    exact (canonical7249 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1267 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (2 : Fin 3) = raw7223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw7223; decide +kernel
    rw [heq]
    exact (canonical7223 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1267 + (injectiveMoment H (mergeFirst pivotMatrix1267 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1267 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1267 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1267, value174, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound1272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1272 = Sparse.eval value1272 (momentVector H) := by
  have heq : pivotMatrix1272 = (fun u v => node1272.transpose (pivotPermutation1272 u) v) := by apply Matrix.ext; unfold pivotMatrix1272 node1272 pivotPermutation1272; decide +kernel
  have hmoment : injectiveMoment H node1272 = injectiveMoment H pivotMatrix1272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1272 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1272 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1272 (0 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1272 (0 : Fin 3) = raw7480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1272 raw7480; decide +kernel
    rw [heq]
    exact (canonical7480 hH).trans (sound286 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1272 (1 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1272 (1 : Fin 3) = raw9746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1272 raw9746; decide +kernel
    rw [heq]
    exact (canonical9746 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1272 (2 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1272 (2 : Fin 3) = raw9761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1272 raw9761; decide +kernel
    rw [heq]
    exact (canonical9761 hH).trans (sound286 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1272 + (injectiveMoment H (mergeFirst pivotMatrix1272 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1272 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1272 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1272, value281, value286, Sparse.eval] at hc ⊢
  linarith

theorem sound1278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1278 = Sparse.eval value1278 (momentVector H) := by
  have heq : pivotMatrix1278 = (fun u v => node1278.transpose (pivotPermutation1278 u) v) := by apply Matrix.ext; unfold pivotMatrix1278 node1278 pivotPermutation1278; decide +kernel
  have hmoment : injectiveMoment H node1278 = injectiveMoment H pivotMatrix1278 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1278 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1278 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1278 (0 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1278 (0 : Fin 3) = raw7915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1278 raw7915; decide +kernel
    rw [heq]
    exact (canonical7915 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1278 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1278 (1 : Fin 3) = raw10099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1278 raw10099; decide +kernel
    rw [heq]
    exact (canonical10099 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1278 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1278 (2 : Fin 3) = raw10105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1278 raw10105; decide +kernel
    rw [heq]
    exact (canonical10105 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1278 + (injectiveMoment H (mergeFirst pivotMatrix1278 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1278 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1278 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1278, value206, value225, value246, Sparse.eval] at hc ⊢
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

theorem sound1306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1306 = Sparse.eval value1306 (momentVector H) := by
  have heq : pivotMatrix1306 = (fun u v => node1306.transpose (pivotPermutation1306 u) v) := by apply Matrix.ext; unfold pivotMatrix1306 node1306 pivotPermutation1306; decide +kernel
  have hmoment : injectiveMoment H node1306 = injectiveMoment H pivotMatrix1306 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1306 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1306 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1306 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1306 (0 : Fin 3) = raw6947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1306 raw6947; decide +kernel
    rw [heq]
    exact (canonical6947 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1306 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1306 (1 : Fin 3) = raw8925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1306 raw8925; decide +kernel
    rw [heq]
    exact (canonical8925 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1306 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1306 (2 : Fin 3) = raw8930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1306 raw8930; decide +kernel
    rw [heq]
    exact (canonical8930 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1306 + (injectiveMoment H (mergeFirst pivotMatrix1306 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1306 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1306 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1306, value201, value206, Sparse.eval] at hc ⊢
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

theorem sound586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node586 = Sparse.eval value586 (momentVector H) := by
  have hc : momentVector H 517 = injectiveMoment H node586 := rfl
  simp [value586, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound24
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1555 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1555 = Sparse.eval value1555 (momentVector H) := by
  have heq : pivotMatrix1555 = (fun u v => node1555 (pivotPermutation1555 u) v) := by apply Matrix.ext; unfold pivotMatrix1555 node1555 pivotPermutation1555; decide +kernel
  have hmoment : injectiveMoment H node1555 = injectiveMoment H pivotMatrix1555 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1555 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1555 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1555 (0 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (0 : Fin 4) = raw1128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1128; decide +kernel
    rw [heq]
    exact (canonical1128 hH).trans (sound1070 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1555 (1 : Fin 4)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (1 : Fin 4) = raw1526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1526; decide +kernel
    rw [heq]
    exact (canonical1526 hH).trans (sound286 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1555 (2 : Fin 4)) =
      Sparse.eval value1272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (2 : Fin 4) = raw1664 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1664; decide +kernel
    rw [heq]
    exact (canonical1664 hH).trans (sound1272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1555 (3 : Fin 4)) =
      Sparse.eval value981 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (3 : Fin 4) = raw1667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1667; decide +kernel
    rw [heq]
    exact (canonical1667 hH).trans (sound981 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1555 + (injectiveMoment H (mergeFirst pivotMatrix1555 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1555 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1555 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1555 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1555, value1070, value1272, value286, value981, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1940 = Sparse.eval value1940 (momentVector H) := by
  have heq : pivotMatrix1940 = (fun u v => node1940 (pivotPermutation1940 u) v) := by apply Matrix.ext; unfold pivotMatrix1940 node1940 pivotPermutation1940; decide +kernel
  have hmoment : injectiveMoment H node1940 = injectiveMoment H pivotMatrix1940 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1940 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1940 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1940 (0 : Fin 4)) =
      Sparse.eval value1251 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (0 : Fin 4) = raw4291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw4291; decide +kernel
    rw [heq]
    exact (canonical4291 hH).trans (sound1251 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1940 (1 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (1 : Fin 4) = raw3064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw3064; decide +kernel
    rw [heq]
    exact (canonical3064 hH).trans (sound1171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1940 (2 : Fin 4)) =
      Sparse.eval value586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (2 : Fin 4) = raw3057 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw3057; decide +kernel
    rw [heq]
    exact (canonical3057 hH).trans (sound586 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1940 (3 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (3 : Fin 4) = raw3056 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw3056; decide +kernel
    rw [heq]
    exact (canonical3056 hH).trans (sound1306 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1940 + (injectiveMoment H (mergeFirst pivotMatrix1940 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1940 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1940 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1940 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1940, value1171, value1251, value1306, value586, Sparse.eval] at hc ⊢
  linarith

theorem sound1941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1941 = Sparse.eval value1941 (momentVector H) := by
  have heq : pivotMatrix1941 = (fun u v => node1941 (pivotPermutation1941 u) v) := by apply Matrix.ext; unfold pivotMatrix1941 node1941 pivotPermutation1941; decide +kernel
  have hmoment : injectiveMoment H node1941 = injectiveMoment H pivotMatrix1941 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1941 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1941 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1941 (0 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (0 : Fin 4) = raw2042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw2042; decide +kernel
    rw [heq]
    exact (canonical2042 hH).trans (sound1080 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1941 (1 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (1 : Fin 4) = raw3116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw3116; decide +kernel
    rw [heq]
    exact (canonical3116 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1941 (2 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (2 : Fin 4) = raw3213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw3213; decide +kernel
    rw [heq]
    exact (canonical3213 hH).trans (sound1278 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1941 (3 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (3 : Fin 4) = raw3217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw3217; decide +kernel
    rw [heq]
    exact (canonical3217 hH).trans (sound985 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1941 + (injectiveMoment H (mergeFirst pivotMatrix1941 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1941 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1941 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1941 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1941, value1080, value1278, value246, value985, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound42
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2746 = Sparse.eval value2746 (momentVector H) := by
  have heq : pivotMatrix2746 = (fun u v => node2746 (pivotPermutation2746 u) v) := by apply Matrix.ext; unfold pivotMatrix2746 node2746 pivotPermutation2746; decide +kernel
  have hmoment : injectiveMoment H node2746 = injectiveMoment H pivotMatrix2746 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2746 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2746 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2746 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (0 : Fin 4) = raw5994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw5994; decide +kernel
    rw [heq]
    exact (canonical5994 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2746 (1 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (1 : Fin 4) = raw8269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw8269; decide +kernel
    rw [heq]
    exact (canonical8269 hH).trans (sound977 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2746 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (2 : Fin 4) = raw8270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw8270; decide +kernel
    rw [heq]
    exact (canonical8270 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2746 (3 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (3 : Fin 4) = raw8271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw8271; decide +kernel
    rw [heq]
    exact (canonical8271 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2746 + (injectiveMoment H (mergeFirst pivotMatrix2746 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2746 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2746 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2746 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2746, value1063, value1267, value63, value977, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound48
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3124_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3124 = Sparse.eval value3124 (momentVector H) := by
  have heq : pivotMatrix3124 = (fun u v => node3124 (pivotPermutation3124 u) v) := by apply Matrix.ext; unfold pivotMatrix3124 node3124 pivotPermutation3124; decide +kernel
  have hmoment : injectiveMoment H node3124 = injectiveMoment H pivotMatrix3124 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3124 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3124 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3124 (0 : Fin 5)) =
      Sparse.eval value1555 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3124 (0 : Fin 5) = raw1468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3124 raw1468; decide +kernel
    rw [heq]
    exact (canonical1468 hH).trans (sound1555 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3124 (1 : Fin 5)) =
      Sparse.eval value1940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3124 (1 : Fin 5) = raw3055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3124 raw3055; decide +kernel
    rw [heq]
    exact (canonical3055 hH).trans (sound1940 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3124 (2 : Fin 5)) =
      Sparse.eval value2492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3124 (2 : Fin 5) = raw3065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3124 raw3065; decide +kernel
    rw [heq]
    exact (canonical3065 hH).trans (sound2492_e hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3124 (3 : Fin 5)) =
      Sparse.eval value1941 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3124 (3 : Fin 5) = raw3066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3124 raw3066; decide +kernel
    rw [heq]
    exact (canonical3066 hH).trans (sound1941 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3124 (4 : Fin 5)) =
      Sparse.eval value2746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3124 (4 : Fin 5) = raw3067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3124 raw3067; decide +kernel
    rw [heq]
    exact (canonical3067 hH).trans (sound2746 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3124 + (injectiveMoment H (mergeFirst pivotMatrix3124 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3124 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3124 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3124 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3124 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3124, value1555, value1940, value1941, value2492, value2746, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3124_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3124_e_oai
